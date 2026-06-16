const COAST_DATA_URL = "data/ne_50m_coastline/ne_50m_coastline.shp";
const LAND_DATA_URL = "data/ne_50m_land/ne_50m_land.shp";
const ROUND_COUNT = 10;
const MAX_ROUND_SCORE = 100;
const EARTH_RADIUS_KM = 6371;
const SAMPLING_WEIGHT_EXPONENT = 0.3;
const MIN_QUESTION_LATITUDE = -65;
const MAX_QUESTION_LATITUDE = 65;
const MIN_ROUND_SEPARATION_KM = 1500;
const MIN_RECENT_SEPARATION_KM = 1000;
const LAND_RATIO_SAMPLE_WIDTH = 160;
const RECENT_QUESTION_LIMIT = 40;
const RECENT_QUESTION_STORAGE_KEY = "coastguesser-recent-questions";

const DIFFICULTIES = {
  easy: {
    label: "쉬움",
    widthKm: 1500,
    minCoastlineLengthKm: 300,
    scoreDecayDistanceKm: 6000,
    minLandOrWaterRatio: 0.15
  },
  normal: {
    label: "보통",
    widthKm: 1000,
    minCoastlineLengthKm: 100,
    scoreDecayDistanceKm: 5000,
    minLandOrWaterRatio: 0.1
  },
  hard: {
    label: "어려움",
    widthKm: 600,
    minCoastlineLengthKm: 50,
    scoreDecayDistanceKm: 4000,
    minLandOrWaterRatio: 0
  }
};

const state = {
  round: 0,
  score: 0,
  guess: null,
  answered: false,
  ready: false,
  hasStarted: false,
  timerId: null,
  timerStartedAt: null,
  elapsedMs: 0,
  difficultyKey: "normal",
  rounds: [],
  coastSource: null,
  coast: null,
  land: null
};

const $ = (selector) => document.querySelector(selector);
const canvas = $("#coastCanvas");
const ctx = canvas.getContext("2d");
const worldCanvas = $("#worldBase");
const worldCtx = worldCanvas.getContext("2d");
const worldMap = $("#worldMap");
const guessPin = $("#guessPin");
const resultLayer = $("#resultLayer");

function normalizeLongitudeDelta(value) {
  let result = value;
  while (result > 180) result -= 360;
  while (result < -180) result += 360;
  return result;
}

function segmentDistance(lat1, lng1, lat2, lng2) {
  const meanLat = ((lat1 + lat2) / 2) * Math.PI / 180;
  const dx = normalizeLongitudeDelta(lng2 - lng1) * 111.32 * Math.cos(meanLat);
  const dy = (lat2 - lat1) * 111.32;
  return Math.hypot(dx, dy);
}

function parseShapeData(buffer, expectedShapeType) {
  const view = new DataView(buffer);
  const lines = [];
  let totalLength = 0;
  let offset = 100;

  while (offset + 12 <= buffer.byteLength) {
    const contentBytes = view.getInt32(offset + 4, false) * 2;
    const recordStart = offset + 8;
    const recordEnd = recordStart + contentBytes;

    if (recordEnd > buffer.byteLength) break;
    if (view.getInt32(recordStart, true) === expectedShapeType) {
      const partCount = view.getInt32(recordStart + 36, true);
      const pointCount = view.getInt32(recordStart + 40, true);
      const partsOffset = recordStart + 44;
      const pointsOffset = partsOffset + partCount * 4;

      for (let part = 0; part < partCount; part += 1) {
        const start = view.getInt32(partsOffset + part * 4, true);
        const end = part + 1 < partCount
          ? view.getInt32(partsOffset + (part + 1) * 4, true)
          : pointCount;
        const count = end - start;
        if (count < 2) continue;

        const pointOffset = pointsOffset + start * 16;
        let minLng = Infinity;
        let minLat = Infinity;
        let maxLng = -Infinity;
        let maxLat = -Infinity;
        let length = 0;
        let previousLng = view.getFloat64(pointOffset, true);
        let previousLat = view.getFloat64(pointOffset + 8, true);

        minLng = maxLng = previousLng;
        minLat = maxLat = previousLat;

        for (let index = 1; index < count; index += 1) {
          const point = pointOffset + index * 16;
          const lng = view.getFloat64(point, true);
          const lat = view.getFloat64(point + 8, true);
          minLng = Math.min(minLng, lng);
          maxLng = Math.max(maxLng, lng);
          minLat = Math.min(minLat, lat);
          maxLat = Math.max(maxLat, lat);
          length += segmentDistance(previousLat, previousLng, lat, lng);
          previousLng = lng;
          previousLat = lat;
        }

        const lastOffset = pointOffset + (count - 1) * 16;
        const closed =
          Math.abs(view.getFloat64(pointOffset, true) - view.getFloat64(lastOffset, true)) < 1e-8
          && Math.abs(view.getFloat64(pointOffset + 8, true) - view.getFloat64(lastOffset + 8, true)) < 1e-8;

        totalLength += length;
        lines.push({
          pointOffset,
          count,
          minLng,
          minLat,
          maxLng,
          maxLat,
          length,
          cumulativeLength: totalLength,
          closed
        });
      }
    }

    offset = recordEnd;
  }

  return { buffer, view, lines, totalLength };
}

function prepareCoastlineSamplingPool(dataset, minimumLengthKm) {
  let totalSamplingWeight = 0;
  const samplingLines = dataset.lines
    .filter((line) => line.length >= minimumLengthKm)
    .map((line) => {
      const samplingWeight = Math.pow(line.length, SAMPLING_WEIGHT_EXPONENT);
      totalSamplingWeight += samplingWeight;
      return {
        ...line,
        samplingWeight,
        cumulativeSamplingWeight: totalSamplingWeight
      };
    });

  return {
    ...dataset,
    samplingLines,
    totalSamplingWeight
  };
}

function findWeightedLine(target) {
  const lines = state.coast.samplingLines;
  let low = 0;
  let high = lines.length - 1;

  while (low < high) {
    const middle = Math.floor((low + high) / 2);
    if (lines[middle].cumulativeSamplingWeight < target) low = middle + 1;
    else high = middle;
  }
  return lines[low];
}

function randomCoastalPoint() {
  for (let attempt = 0; attempt < 100; attempt += 1) {
    const target = Math.random() * state.coast.totalSamplingWeight;
    const line = findWeightedLine(target);
    let remaining = Math.random() * line.length;
    const view = state.coast.view;

    for (let index = 1; index < line.count; index += 1) {
      const previous = line.pointOffset + (index - 1) * 16;
      const current = line.pointOffset + index * 16;
      const lng1 = view.getFloat64(previous, true);
      const lat1 = view.getFloat64(previous + 8, true);
      const lng2 = view.getFloat64(current, true);
      const lat2 = view.getFloat64(current + 8, true);
      const length = segmentDistance(lat1, lng1, lat2, lng2);

      if (remaining <= length || index === line.count - 1) {
        const ratio = length > 0 ? Math.min(1, remaining / length) : 0;
        const lngDelta = normalizeLongitudeDelta(lng2 - lng1);
        const lng = normalizeLongitudeDelta(lng1 + lngDelta * ratio);
        const lat = lat1 + (lat2 - lat1) * ratio;
        if (lat < MIN_QUESTION_LATITUDE || lat > MAX_QUESTION_LATITUDE) break;

        const widthKm = DIFFICULTIES[state.difficultyKey].widthKm;
        const offsetXKm = (Math.random() - 0.5) * widthKm * 0.18;
        const offsetYKm = (Math.random() - 0.5) * widthKm * 0.12;
        const cosLat = Math.max(0.08, Math.cos(lat * Math.PI / 180));

        return {
          lat,
          lng,
          widthKm,
          centerLat: Math.max(-89, Math.min(89, lat + offsetYKm / 111.32)),
          centerLng: normalizeLongitudeDelta(lng + offsetXKm / (111.32 * cosLat))
        };
      }
      remaining -= length;
    }
  }

  throw new Error("Failed to sample a coastline within the latitude limits.");
}

function projectPointToSize(lng, lat, round, width, height) {
  const kmPerLngDegree = 111.32 * Math.max(0.08, Math.cos(round.centerLat * Math.PI / 180));
  const dx = normalizeLongitudeDelta(lng - round.centerLng) * kmPerLngDegree;
  const dy = (lat - round.centerLat) * 111.32;
  const scale = width / round.widthKm;
  return [width / 2 + dx * scale, height / 2 - dy * scale];
}

function calculateLandRatio(round) {
  const aspect = canvas.width / canvas.height;
  const width = LAND_RATIO_SAMPLE_WIDTH;
  const height = Math.round(width / aspect);
  const maskCanvas = document.createElement("canvas");
  maskCanvas.width = width;
  maskCanvas.height = height;
  const maskContext = maskCanvas.getContext("2d", { willReadFrequently: true });
  const visibleLand = visibleLinesForRound(round, state.land);

  maskContext.fillStyle = "black";
  maskContext.fillRect(0, 0, width, height);
  maskContext.fillStyle = "white";
  maskContext.beginPath();
  visibleLand.forEach((line) => {
    traceLine(
      maskContext,
      line,
      state.land,
      (lng, lat) => projectPointToSize(lng, lat, round, width, height),
      0.15
    );
  });
  maskContext.fill("evenodd");

  const pixels = maskContext.getImageData(0, 0, width, height).data;
  let landPixels = 0;
  for (let index = 0; index < pixels.length; index += 4) {
    if (pixels[index] > 127) landPixels += 1;
  }
  return landPixels / (width * height);
}

function hasBalancedLandAndWater(round) {
  const minimumRatio = DIFFICULTIES[state.difficultyKey].minLandOrWaterRatio;
  if (minimumRatio <= 0) return true;
  const landRatio = calculateLandRatio(round);
  return landRatio >= minimumRatio && landRatio <= 1 - minimumRatio;
}

function loadRecentQuestions() {
  try {
    const stored = JSON.parse(localStorage.getItem(RECENT_QUESTION_STORAGE_KEY) || "[]");
    return Array.isArray(stored)
      ? stored.filter((point) => Number.isFinite(point.lat) && Number.isFinite(point.lng))
      : [];
  } catch {
    return [];
  }
}

function saveRecentQuestions(rounds) {
  const recent = [...loadRecentQuestions(), ...rounds]
    .slice(-RECENT_QUESTION_LIMIT)
    .map(({ lat, lng }) => ({ lat, lng }));
  localStorage.setItem(RECENT_QUESTION_STORAGE_KEY, JSON.stringify(recent));
}

function makeRandomRounds() {
  const rounds = [];
  const recentQuestions = loadRecentQuestions();
  let attempts = 0;

  while (rounds.length < ROUND_COUNT && attempts < 1000) {
    const candidate = randomCoastalPoint();
    const separatedFromRound = rounds.every(
      (round) => haversine(round, candidate) > MIN_ROUND_SEPARATION_KM
    );
    const separatedFromRecent = recentQuestions.every(
      (round) => haversine(round, candidate) > MIN_RECENT_SEPARATION_KM
    );
    if (separatedFromRound && separatedFromRecent && hasBalancedLandAndWater(candidate)) {
      rounds.push(candidate);
    }
    attempts += 1;
  }

  while (rounds.length < ROUND_COUNT && attempts < 2000) {
    const candidate = randomCoastalPoint();
    const separated = rounds.every(
      (round) => haversine(round, candidate) > MIN_ROUND_SEPARATION_KM
    );
    if (separated && hasBalancedLandAndWater(candidate)) rounds.push(candidate);
    attempts += 1;
  }

  while (rounds.length < ROUND_COUNT && attempts < 5000) {
    const candidate = randomCoastalPoint();
    if (hasBalancedLandAndWater(candidate)) rounds.push(candidate);
    attempts += 1;
  }
  while (rounds.length < ROUND_COUNT) rounds.push(randomCoastalPoint());
  saveRecentQuestions(rounds);
  return rounds;
}

function longitudeBoundsOverlap(line, centerLng, halfDegrees) {
  const targetMin = centerLng - halfDegrees;
  const targetMax = centerLng + halfDegrees;
  return [-360, 0, 360].some((shift) =>
    line.maxLng + shift >= targetMin && line.minLng + shift <= targetMax
  );
}

function visibleLinesForRound(round, dataset) {
  const aspect = canvas.width / canvas.height;
  const halfWidthDegrees = round.widthKm / (2 * 111.32 * Math.max(0.08, Math.cos(round.centerLat * Math.PI / 180)));
  const halfHeightDegrees = round.widthKm / aspect / (2 * 111.32);
  const padding = 1.25;
  const minLat = round.centerLat - halfHeightDegrees * padding;
  const maxLat = round.centerLat + halfHeightDegrees * padding;

  return dataset.lines.filter((line) =>
    line.maxLat >= minLat
    && line.minLat <= maxLat
    && longitudeBoundsOverlap(line, round.centerLng, halfWidthDegrees * padding)
  );
}

function projectPoint(lng, lat, round) {
  return projectPointToSize(lng, lat, round, canvas.width, canvas.height);
}

function traceLine(context, line, dataset, projector, simplifyPixels = 0) {
  const view = dataset.view;
  let previousX = Infinity;
  let previousY = Infinity;
  let started = false;

  for (let index = 0; index < line.count; index += 1) {
    const pointOffset = line.pointOffset + index * 16;
    const lng = view.getFloat64(pointOffset, true);
    const lat = view.getFloat64(pointOffset + 8, true);
    const [x, y] = projector(lng, lat);
    const isLast = index === line.count - 1;

    if (
      started
      && !isLast
      && simplifyPixels > 0
      && Math.abs(x - previousX) < simplifyPixels
      && Math.abs(y - previousY) < simplifyPixels
    ) {
      continue;
    }

    if (!started) {
      context.moveTo(x, y);
      started = true;
    } else {
      context.lineTo(x, y);
    }
    previousX = x;
    previousY = y;
  }

  if (line.closed) context.closePath();
}

function renderCoast(round) {
  const { width, height } = canvas;
  const visibleCoastlines = visibleLinesForRound(round, state.coast);
  const visibleLand = visibleLinesForRound(round, state.land);
  const ocean = ctx.createLinearGradient(0, 0, width, height);
  ocean.addColorStop(0, "#5b9fac");
  ocean.addColorStop(0.55, "#3e8492");
  ocean.addColorStop(1, "#246b79");
  ctx.fillStyle = ocean;
  ctx.fillRect(0, 0, width, height);

  ctx.save();
  ctx.globalAlpha = 0.15;
  ctx.strokeStyle = "#dff4ef";
  ctx.lineWidth = 2;
  for (let y = 40; y < height; y += 48) {
    ctx.beginPath();
    ctx.moveTo(0, y);
    ctx.bezierCurveTo(width * 0.3, y - 8, width * 0.7, y + 8, width, y);
    ctx.stroke();
  }
  ctx.restore();

  const land = ctx.createLinearGradient(0, 0, width, height);
  land.addColorStop(0, "#b7b886");
  land.addColorStop(0.45, "#7f9669");
  land.addColorStop(1, "#496c58");

  ctx.fillStyle = land;
  ctx.beginPath();
  visibleLand.forEach((line) => {
    traceLine(ctx, line, state.land, (lng, lat) => projectPoint(lng, lat, round), 0.3);
  });
  ctx.fill("evenodd");

  ctx.save();
  ctx.strokeStyle = "rgba(242, 226, 176, 0.74)";
  ctx.lineWidth = 18;
  ctx.lineJoin = "round";
  ctx.lineCap = "round";
  visibleCoastlines.forEach((line) => {
    ctx.beginPath();
    traceLine(ctx, line, state.coast, (lng, lat) => projectPoint(lng, lat, round), 0.25);
    ctx.stroke();
  });
  ctx.strokeStyle = "rgba(255, 255, 255, 0.76)";
  ctx.lineWidth = 5;
  visibleCoastlines.forEach((line) => {
    ctx.beginPath();
    traceLine(ctx, line, state.coast, (lng, lat) => projectPoint(lng, lat, round), 0.2);
    ctx.stroke();
  });
  ctx.restore();

  const vignette = ctx.createRadialGradient(
    width / 2,
    height / 2,
    height * 0.22,
    width / 2,
    height / 2,
    width * 0.75
  );
  vignette.addColorStop(0, "rgba(3, 29, 28, 0)");
  vignette.addColorStop(1, "rgba(3, 29, 28, 0.32)");
  ctx.fillStyle = vignette;
  ctx.fillRect(0, 0, width, height);

  ctx.save();
  ctx.globalCompositeOperation = "soft-light";
  ctx.globalAlpha = 0.18;
  for (let y = 0; y < height; y += 6) ctx.fillRect(0, y, width, 1);
  ctx.restore();

  const scaleKm = Math.max(10, Math.round(round.widthKm / 5 / 10) * 10);
  $("#scaleLabel").textContent = `${scaleKm} KM`;
  const scaleBar = $(".scale-bar span");
  scaleBar.style.width = `${Math.max(42, Math.min(140, (scaleKm / round.widthKm) * 100))}px`;
}

function renderWorldMap() {
  const { width, height } = worldCanvas;
  worldCtx.clearRect(0, 0, width, height);
  worldCtx.fillStyle = "#a7bdb2";
  worldCtx.strokeStyle = "#6f8b80";
  worldCtx.lineWidth = 2;
  worldCtx.lineJoin = "round";

  const projector = (lng, lat) => [
    ((lng + 180) / 360) * width,
    ((90 - lat) / 180) * height
  ];

  worldCtx.beginPath();
  state.land.lines.forEach((line) => {
    traceLine(worldCtx, line, state.land, projector, 1.1);
  });
  worldCtx.fill("evenodd");

  state.coast.lines.forEach((line) => {
    worldCtx.beginPath();
    traceLine(worldCtx, line, state.coast, projector, 1.1);
    worldCtx.stroke();
  });
}

function latLngToMap(lat, lng) {
  return {
    x: ((lng + 180) / 360) * 1000,
    y: ((90 - lat) / 180) * 500
  };
}

function mapToLatLng(x, y) {
  return {
    lat: 90 - (y / 500) * 180,
    lng: (x / 1000) * 360 - 180
  };
}

function formatCoordinate({ lat, lng }) {
  const latDir = lat >= 0 ? "N" : "S";
  const lngDir = lng >= 0 ? "E" : "W";
  return `${Math.abs(lat).toFixed(3)}° ${latDir}, ${Math.abs(lng).toFixed(3)}° ${lngDir}`;
}

function haversine(a, b) {
  const toRad = (degree) => degree * Math.PI / 180;
  const dLat = toRad(b.lat - a.lat);
  const dLng = toRad(normalizeLongitudeDelta(b.lng - a.lng));
  const h = Math.sin(dLat / 2) ** 2
    + Math.cos(toRad(a.lat)) * Math.cos(toRad(b.lat)) * Math.sin(dLng / 2) ** 2;
  return EARTH_RADIUS_KM * 2 * Math.atan2(Math.sqrt(h), Math.sqrt(1 - h));
}

function scoreForDistance(distance) {
  const decayDistance = DIFFICULTIES[state.difficultyKey].scoreDecayDistanceKm;
  return Math.round(MAX_ROUND_SCORE * Math.exp(-distance / decayDistance));
}

function currentLocation() {
  return state.rounds[state.round];
}

function formatElapsedTime(milliseconds) {
  const totalSeconds = Math.max(0, Math.floor(milliseconds / 1000));
  const minutes = Math.floor(totalSeconds / 60);
  const seconds = totalSeconds % 60;
  return `${String(minutes).padStart(2, "0")}분 ${String(seconds).padStart(2, "0")}초`;
}

function currentElapsedMs() {
  if (!state.timerStartedAt) return state.elapsedMs;
  return Date.now() - state.timerStartedAt;
}

function updateTimerDisplay() {
  $("#gameTimer").textContent = formatElapsedTime(currentElapsedMs());
}

function stopGameTimer() {
  state.elapsedMs = currentElapsedMs();
  state.timerStartedAt = null;
  if (state.timerId) {
    clearInterval(state.timerId);
    state.timerId = null;
  }
  updateTimerDisplay();
  return state.elapsedMs;
}

function startGameTimer() {
  stopGameTimer();
  state.elapsedMs = 0;
  state.timerStartedAt = Date.now();
  updateTimerDisplay();
  state.timerId = setInterval(updateTimerDisplay, 1000);
}

function loadRound() {
  state.guess = null;
  state.answered = false;
  resultLayer.replaceChildren();
  guessPin.setAttribute("visibility", "hidden");
  $("#resultDrawer").classList.remove("open");
  $("#roundNow").textContent = state.round + 1;
  $("#fragmentNumber").textContent = `#${String(state.round + 1).padStart(2, "0")}`;
  $("#selectedCoordinates").textContent = "아직 선택하지 않았습니다";
  $("#guessButton").disabled = true;
  $("#guessButtonLabel").textContent = "위치를 먼저 선택하세요";
  $("#resetPin").disabled = true;
  $("#mapInstruction").style.opacity = "1";
  renderCoast(currentLocation());
}

function placeGuess(event) {
  if (!state.ready || state.answered) return;
  const point = worldMap.createSVGPoint();
  point.x = event.clientX;
  point.y = event.clientY;
  const svgPoint = point.matrixTransform(worldMap.getScreenCTM().inverse());
  const x = Math.max(0, Math.min(1000, svgPoint.x));
  const y = Math.max(0, Math.min(500, svgPoint.y));
  state.guess = mapToLatLng(x, y);
  guessPin.setAttribute("transform", `translate(${x} ${y})`);
  guessPin.setAttribute("visibility", "visible");
  $("#selectedCoordinates").textContent = formatCoordinate(state.guess);
  $("#guessButton").disabled = false;
  $("#guessButtonLabel").textContent = "이 위치로 추측하기";
  $("#resetPin").disabled = false;
  $("#mapInstruction").style.opacity = "0";
}

function resetGuess() {
  if (state.answered) return;
  state.guess = null;
  guessPin.setAttribute("visibility", "hidden");
  $("#selectedCoordinates").textContent = "아직 선택하지 않았습니다";
  $("#guessButton").disabled = true;
  $("#guessButtonLabel").textContent = "위치를 먼저 선택하세요";
  $("#resetPin").disabled = true;
  $("#mapInstruction").style.opacity = "1";
}

function createSvgElement(name, attributes) {
  const element = document.createElementNS("http://www.w3.org/2000/svg", name);
  Object.entries(attributes).forEach(([key, value]) => element.setAttribute(key, value));
  return element;
}

function revealAnswer() {
  if (!state.guess || state.answered) return;
  state.answered = true;
  const answer = currentLocation();
  const distance = haversine(state.guess, answer);
  const roundScore = scoreForDistance(distance);
  state.score += roundScore;
  $("#totalScore").textContent = state.score.toLocaleString("ko-KR");
  if (state.round === state.rounds.length - 1) stopGameTimer();

  const guessPoint = latLngToMap(state.guess.lat, state.guess.lng);
  const answerPoint = latLngToMap(answer.lat, answer.lng);
  const deltaX = Math.abs(answerPoint.x - guessPoint.x);
  const crossesDateline = deltaX > 500;

  if (!crossesDateline) {
    const midX = (guessPoint.x + answerPoint.x) / 2;
    const curve = Math.min(80, deltaX * 0.12 + 20);
    resultLayer.append(createSvgElement("path", {
      d: `M ${guessPoint.x} ${guessPoint.y} Q ${midX} ${Math.min(490, (guessPoint.y + answerPoint.y) / 2 + curve)} ${answerPoint.x} ${answerPoint.y}`,
      class: "answer-line"
    }));
  }

  resultLayer.append(
    createSvgElement("circle", {
      cx: answerPoint.x,
      cy: answerPoint.y,
      r: 17,
      class: "answer-ring"
    }),
    createSvgElement("circle", {
      cx: answerPoint.x,
      cy: answerPoint.y,
      r: 8,
      class: "answer-dot"
    })
  );

  $("#resultName").textContent = formatCoordinate(answer);
  $("#resultDifficulty").textContent = DIFFICULTIES[state.difficultyKey].label;
  $("#resultFact").textContent =
    `Natural Earth 1:50m 실제 해안선 · ${DIFFICULTIES[state.difficultyKey].label} · 화면 폭 ${Math.round(answer.widthKm)} km`;
  $("#resultDistance").textContent = `${Math.round(distance).toLocaleString("ko-KR")} km`;
  $("#roundScore").textContent = roundScore.toLocaleString("ko-KR");
  $("#nextButton span:first-child").textContent =
    state.round === state.rounds.length - 1 ? "최종 결과 보기" : "다음 해안선";
  $("#resultDrawer").classList.add("open");
  $("#guessButton").disabled = true;
  $("#resetPin").disabled = true;
}

function nextRound() {
  if (state.round < state.rounds.length - 1) {
    state.round += 1;
    loadRound();
    window.scrollTo({ top: 0, behavior: "smooth" });
    return;
  }
  showEndScreen();
}

function showEndScreen() {
  $("#resultDrawer").classList.remove("open");
  if (state.timerStartedAt) stopGameTimer();
  $("#finalScore").textContent = state.score.toLocaleString("ko-KR");
  $("#finalTime").textContent = formatElapsedTime(state.elapsedMs);
  $("#endDifficulty").textContent = DIFFICULTIES[state.difficultyKey].label;
  const ratio = state.score / (ROUND_COUNT * MAX_ROUND_SCORE);
  $("#endMessage").textContent = ratio > 0.75
    ? "놀라운 해안 감각입니다. 전 세계의 작은 곡선까지 정확히 읽어냈어요."
    : ratio > 0.45
      ? "좋은 항해였습니다. 실제 해안선의 패턴이 눈에 들어오기 시작했네요."
      : "전 세계 무작위 해안은 만만치 않죠. 다음 게임에는 완전히 새로운 지점들이 나옵니다.";
  $("#endModal").hidden = false;
}

function updateDifficultySelection() {
  document.querySelectorAll("[data-difficulty]").forEach((button) => {
    const selected = button.dataset.difficulty === state.difficultyKey;
    button.classList.toggle("selected", selected);
    button.setAttribute("aria-pressed", String(selected));
  });
}

function openDifficultyModal() {
  updateDifficultySelection();
  $("#difficultyModal").hidden = false;
  $("#closeDifficulty").hidden = !state.hasStarted;
}

function startGame(difficultyKey = state.difficultyKey) {
  if (!state.ready) return;
  state.difficultyKey = difficultyKey;
  const difficulty = DIFFICULTIES[difficultyKey];
  state.coast = prepareCoastlineSamplingPool(
    state.coastSource,
    difficulty.minCoastlineLengthKm
  );
  state.hasStarted = true;
  state.round = 0;
  state.score = 0;
  state.rounds = makeRandomRounds();
  $("#totalScore").textContent = "0";
  $("#finalTime").textContent = formatElapsedTime(0);
  $("#difficultyLabel").textContent = difficulty.label;
  updateDifficultySelection();
  $("#difficultyModal").hidden = true;
  $("#endModal").hidden = true;
  startGameTimer();
  loadRound();
}

async function initialize() {
  try {
    const [coastResponse, landResponse] = await Promise.all([
      fetch(COAST_DATA_URL),
      fetch(LAND_DATA_URL)
    ]);
    if (!coastResponse.ok || !landResponse.ok) {
      throw new Error(`HTTP ${coastResponse.status}/${landResponse.status}`);
    }
    const [coastBuffer, landBuffer] = await Promise.all([
      coastResponse.arrayBuffer(),
      landResponse.arrayBuffer()
    ]);
    state.coastSource = parseShapeData(coastBuffer, 3);
    state.coast = prepareCoastlineSamplingPool(
      state.coastSource,
      DIFFICULTIES[state.difficultyKey].minCoastlineLengthKm
    );
    state.land = parseShapeData(landBuffer, 5);
    renderWorldMap();
    state.ready = true;
    $("#loadingState").classList.add("hidden");
    $("#mapWrap").classList.remove("is-loading");
    openDifficultyModal();
    $("#closeDifficulty").hidden = true;
  } catch (error) {
    console.error("Coastline data failed to load:", error);
    $("#loadingState").textContent = "해안선 데이터를 불러오지 못했습니다. 로컬 서버로 실행해 주세요.";
    $("#guessButtonLabel").textContent = "데이터 로드 실패";
  }
}

worldMap.addEventListener("click", placeGuess);
$("#resetPin").addEventListener("click", resetGuess);
$("#guessButton").addEventListener("click", revealAnswer);
$("#nextButton").addEventListener("click", nextRound);
$("#restartButton").addEventListener("click", () => {
  $("#endModal").hidden = true;
  openDifficultyModal();
});

$("#difficultyButton").addEventListener("click", openDifficultyModal);
$("#closeDifficulty").addEventListener("click", () => {
  if (state.hasStarted) $("#difficultyModal").hidden = true;
});
document.querySelectorAll("[data-difficulty]").forEach((button) => {
  button.addEventListener("click", () => startGame(button.dataset.difficulty));
});

$("#helpButton").addEventListener("click", () => {
  $("#helpModal").hidden = false;
});
$("#closeHelp").addEventListener("click", () => {
  $("#helpModal").hidden = true;
});
$("#startPlaying").addEventListener("click", () => {
  $("#helpModal").hidden = true;
});
$("#helpModal").addEventListener("click", (event) => {
  if (event.target === $("#helpModal")) $("#helpModal").hidden = true;
});

document.addEventListener("keydown", (event) => {
  if (event.key === "Escape") {
    $("#helpModal").hidden = true;
    if (state.hasStarted) $("#difficultyModal").hidden = true;
  }
  if (event.key === "Enter" && state.guess && !state.answered) revealAnswer();
});

initialize();
