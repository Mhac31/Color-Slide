"use strict";

const COLORS = ["red", "blue", "green", "yellow"];
const BOARD_SIZE = 5;
const BOARD_TILE_COUNT = BOARD_SIZE * BOARD_SIZE;
const TARGET_SIZE = 3;
// Zero-based row-major positions for rows 1-3 and columns 1-3 of the 5x5 board.
const MATCH_ZONE_INDICES = [6, 7, 8, 11, 12, 13, 16, 17, 18];
const EMPTY_TILE = null;
const STARTING_SECONDS = 60;
const SWAP_ANIMATION_MS = 380;
const PUZZLE_TRANSITION_MS = 480;
const SUCCESS_ANIMATION_MS = 1200;
const PUZZLE_SCRAMBLE_MOVES = 100;
const BEST_SCORE_STORAGE_KEY = "colorGridBestScore";

const targetGrid = document.querySelector("#target-grid");
const playerGrid = document.querySelector("#player-grid");
const moveCountDisplay = document.querySelector("#move-count");
const scoreDisplay = document.querySelector("#score");
const bestScoreDisplay = document.querySelector("#best-score");
const puzzleCountDisplay = document.querySelector("#puzzle-count");
const timerDisplay = document.querySelector("#timer");
const timerStat = document.querySelector("#timer-stat");
const statusMessage = document.querySelector("#status-message");
const gridHint = document.querySelector("#grid-hint");
const roundNumberDisplay = document.querySelector("#round-number");
const successOverlay = document.querySelector("#success-overlay");
const successParticles = document.querySelector("#success-particles");
const newHighScoreBanner = document.querySelector("#new-high-score-banner");
const gameOverPanel = document.querySelector("#game-over-panel");
const finalScoreDisplay = document.querySelector("#final-score");
const finalBestScoreDisplay = document.querySelector("#final-best-score");
const finalPuzzlesDisplay = document.querySelector("#final-puzzles");
const finalMovesDisplay = document.querySelector("#final-moves");
const personalBestBanner = document.querySelector("#personal-best-banner");
const playAgainButton = document.querySelector("#play-again-button");
const colorblindToggle = document.querySelector("#colorblind-toggle");
const COLORBLIND_STORAGE_KEY = "colorGridColorblindMode";
const COLOR_MARKS = {
  red: { name: "Red", symbol: "●", letter: "R" },
  blue: { name: "Blue", symbol: "◆", letter: "B" },
  green: { name: "Green", symbol: "▲", letter: "G" },
  yellow: { name: "Yellow", symbol: "★", letter: "Y" },
};

let targetPattern = [];
let playerPattern = [];
let totalMoves = 0;
let score = 0;
let bestScore = loadBestScore();
let puzzlesCompleted = 0;
let remainingSeconds = STARTING_SECONDS;
let timerInterval = null;
let transitionTimeout = null;
let scoreAnimationFrame = null;
const activeSlideAnimations = new WeakMap();
const landingEffectTimeouts = new WeakMap();
let timerStarted = false;
let isTransitioning = false;
let gameOver = false;
let puzzleRewarded = false;
let newHighScoreThisRun = false;
let colorblindMode = true;

function loadBestScore() {
  try {
    const storedScore = window.localStorage.getItem(BEST_SCORE_STORAGE_KEY);
    if (storedScore === null) {
      return 0;
    }

    const savedScore = Number(storedScore);
    if (storedScore.trim() === "" || !Number.isSafeInteger(savedScore) || savedScore < 0) {
      console.warn("[COLOR GRID] The saved best score is invalid; starting with 0.");
      return 0;
    }

    return savedScore;
  } catch (error) {
    console.warn("[COLOR GRID] Could not load the saved best score.", error);
    return 0;
  }
}

function saveBestScore() {
  try {
    window.localStorage.setItem(BEST_SCORE_STORAGE_KEY, String(bestScore));
  } catch (error) {
    console.warn("[COLOR GRID] Could not save the best score.", error);
  }
}

function loadColorblindPreference() {
  try {
    const savedPreference = window.localStorage.getItem(COLORBLIND_STORAGE_KEY);
    return savedPreference === null ? true : savedPreference === "true";
  } catch (error) {
    console.warn("[COLOR GRID] Could not load the colorblind mode preference.", error);
    return true;
  }
}

function saveColorblindPreference(enabled) {
  try {
    window.localStorage.setItem(COLORBLIND_STORAGE_KEY, String(enabled));
  } catch (error) {
    console.warn("[COLOR GRID] Could not save the colorblind mode preference.", error);
  }
}

function applyColorblindMode(enabled) {
  colorblindMode = enabled;
  document.documentElement.classList.toggle("colorblind-mode", colorblindMode);
}

function getColorQuantities(board) {
  return COLORS.reduce((quantities, color) => {
    quantities[color] = board.filter((tileColor) => tileColor === color).length;
    return quantities;
  }, {});
}

// Fisher-Yates keeps every tile while giving it a random new position.
function shufflePattern(pattern) {
  const shuffled = [...pattern];

  for (let index = shuffled.length - 1; index > 0; index -= 1) {
    const swapIndex = Math.floor(Math.random() * (index + 1));
    [shuffled[index], shuffled[swapIndex]] = [shuffled[swapIndex], shuffled[index]];
  }

  return shuffled;
}

// Generate the 24 colored tiles independently from the single empty space.
function makeColorInventory() {
  const inventory = [...COLORS];

  while (inventory.length < BOARD_TILE_COUNT - 1) {
    inventory.push(COLORS[Math.floor(Math.random() * COLORS.length)]);
  }

  return shufflePattern(inventory);
}

// Draw the target from this board's inventory without using any color too often.
function makeTargetPattern(inventory, previousTarget) {
  let pattern;

  do {
    const availableTiles = [...inventory];
    pattern = Array.from({ length: TARGET_SIZE * TARGET_SIZE }, () => {
      const tileIndex = Math.floor(Math.random() * availableTiles.length);
      return availableTiles.splice(tileIndex, 1)[0];
    });
  } while (
    new Set(pattern).size < 2
    || (previousTarget && pattern.every((color, index) => color === previousTarget[index]))
  );

  return pattern;
}

function getAdjacentTileIndices(index) {
  const row = Math.floor(index / BOARD_SIZE);
  const column = index % BOARD_SIZE;
  const adjacent = [];

  if (row > 0) adjacent.push(index - BOARD_SIZE);
  if (row < BOARD_SIZE - 1) adjacent.push(index + BOARD_SIZE);
  if (column > 0) adjacent.push(index - 1);
  if (column < BOARD_SIZE - 1) adjacent.push(index + 1);

  return adjacent;
}

function getSolvedBoard(targetPattern, inventory) {
  const board = Array(BOARD_TILE_COUNT).fill(EMPTY_TILE);
  const remainingInventory = [...inventory];

  MATCH_ZONE_INDICES.forEach((boardIndex, targetIndex) => {
    board[boardIndex] = targetPattern[targetIndex];
    remainingInventory.splice(remainingInventory.indexOf(targetPattern[targetIndex]), 1);
  });

  const outsideIndices = Array.from(
    { length: BOARD_TILE_COUNT },
    (_, index) => index,
  ).filter((index) => !MATCH_ZONE_INDICES.includes(index));

  shufflePattern(outsideIndices).forEach((boardIndex, index) => {
    board[boardIndex] = remainingInventory[index] ?? EMPTY_TILE;
  });

  return board;
}

function getEmptyIndex(board) {
  return board.indexOf(EMPTY_TILE);
}

// Each scramble step is a legal slide from a correctly matched starting board.
function scrambleBoard(board, pattern) {
  let emptyIndex = getEmptyIndex(board);
  let previousEmptyIndex = -1;

  for (let move = 0; move < PUZZLE_SCRAMBLE_MOVES; move += 1) {
    let candidates = getAdjacentTileIndices(emptyIndex)
      .filter((index) => index !== previousEmptyIndex);

    if (candidates.length === 0) {
      candidates = getAdjacentTileIndices(emptyIndex);
    }

    const tileIndex = candidates[Math.floor(Math.random() * candidates.length)];
    [board[emptyIndex], board[tileIndex]] = [board[tileIndex], board[emptyIndex]];
    previousEmptyIndex = emptyIndex;
    emptyIndex = tileIndex;
  }

  while (isCenterSolved(board, pattern)) {
    const candidates = getAdjacentTileIndices(emptyIndex);
    const tileIndex = candidates[Math.floor(Math.random() * candidates.length)];
    [board[emptyIndex], board[tileIndex]] = [board[tileIndex], board[emptyIndex]];
    emptyIndex = tileIndex;
  }

  return board;
}

function checkPattern() {
  const centerPattern = MATCH_ZONE_INDICES.map((boardIndex) => playerPattern[boardIndex]);
  const matches = centerPattern.every((color, index) => {
    return color !== EMPTY_TILE && color === targetPattern[index];
  });

  console.debug("[COLOR GRID] target pattern:", [...targetPattern]);
  console.debug("[COLOR GRID] current center pattern:", centerPattern);
  console.debug("[COLOR GRID] patterns match:", matches);
  console.debug("[COLOR GRID] available color quantities:", getColorQuantities(playerPattern));

  return matches;
}

function isCenterSolved(board, pattern) {
  return MATCH_ZONE_INDICES.every((boardIndex, targetIndex) => {
    return board[boardIndex] !== EMPTY_TILE && board[boardIndex] === pattern[targetIndex];
  });
}

function makePuzzle(previousTarget = null) {
  const inventory = makeColorInventory();
  const pattern = makeTargetPattern(inventory, previousTarget);
  const board = scrambleBoard(getSolvedBoard(pattern, inventory), pattern);

  return {
    target: pattern,
    board,
  };
}

function makeTile(color, index, isInteractive) {
  const tile = document.createElement("button");
  const isMatchZoneTile = isInteractive && MATCH_ZONE_INDICES.includes(index);
  const isEmpty = color === EMPTY_TILE;
  tile.className = `tile ${isEmpty ? "tile-empty" : `tile-${color}`}${isMatchZoneTile ? " is-match-zone" : ""}`;
  tile.type = "button";
  const colorInfo = isEmpty ? null : COLOR_MARKS[color];
  const zoneLabel = isMatchZoneTile ? ", matching zone" : "";
  const targetLabel = isInteractive ? "" : ", target";
  tile.setAttribute(
    "aria-label",
    `${isEmpty ? "Empty space" : `${colorInfo.name} tile${targetLabel}`}, position ${index + 1}${zoneLabel}`,
  );

  if (colorInfo) {
    const mark = document.createElement("span");
    mark.className = "tile-mark";
    mark.setAttribute("aria-hidden", "true");

    const symbol = document.createElement("span");
    symbol.className = "tile-symbol";
    symbol.textContent = colorInfo.symbol;

    const letter = document.createElement("span");
    letter.className = "tile-letter";
    letter.textContent = colorInfo.letter;

    mark.append(symbol, letter);
    tile.append(mark);
  } else {
    tile.disabled = true;
    tile.tabIndex = -1;
  }

  if (isInteractive) {
    tile.dataset.index = String(index);
    tile.setAttribute("aria-pressed", "false");
    tile.disabled = isEmpty || gameOver || isTransitioning;
  } else {
    tile.tabIndex = -1;
    tile.disabled = true;
    tile.setAttribute("aria-hidden", "true");
  }

  return tile;
}

function renderTarget() {
  targetGrid.replaceChildren(
    ...targetPattern.map((color, index) => makeTile(color, index, false)),
  );
  targetGrid.setAttribute("aria-label", "Target 3 by 3 color pattern");
}

function renderPlayerGrid() {
  playerGrid.replaceChildren(
    ...playerPattern.map((color, index) => makeTile(color, index, true)),
  );
}

function updateTileLabels() {
  colorblindToggle.checked = colorblindMode;
  applyColorblindMode(colorblindMode);
}

function setTilesDisabled(disabled) {
  playerGrid.querySelectorAll(".tile").forEach((tile) => {
    tile.disabled = disabled || playerPattern[Number(tile.dataset.index)] === EMPTY_TILE;
  });
}

function formatTime(seconds) {
  const minutes = Math.floor(seconds / 60);
  const remaining = seconds % 60;
  return `${String(minutes).padStart(2, "0")}:${String(remaining).padStart(2, "0")}`;
}

function updateTimerDisplay() {
  timerDisplay.textContent = formatTime(remainingSeconds);
  timerStat.classList.toggle("is-urgent", remainingSeconds <= 10);
}

function startTimer() {
  if (timerInterval !== null || gameOver) {
    return;
  }

  timerStarted = true;
  setStatus("Time is running! Slide tiles to match the target.");
  timerInterval = window.setInterval(() => {
    remainingSeconds = Math.max(0, remainingSeconds - 1);
    updateTimerDisplay();

    if (remainingSeconds === 0) {
      endGame();
    }
  }, 1000);
}

function stopTimer() {
  if (timerInterval !== null) {
    window.clearInterval(timerInterval);
    timerInterval = null;
  }
}

function setStatus(message) {
  statusMessage.lastChild.textContent = ` ${message}`;
}

function getTileFocusScale(isInMatchZone) {
  // Read CSS values so slides use the right scale on desktop and small screens.
  const scaleProperty = isInMatchZone ? "--focus-tile-scale" : "--outer-tile-scale";
  return Number.parseFloat(window.getComputedStyle(playerGrid).getPropertyValue(scaleProperty));
}

// Slide an adjacent colored tile into the empty position and animate its move.
function slideTile(tileIndex, emptyIndex) {
  const tiles = Array.from(playerGrid.children);
  const oldPositions = new Map(
    tiles.map((tile) => [
      tile,
      {
        left: tile.offsetLeft,
        top: tile.offsetTop,
        scale: getTileFocusScale(tile.classList.contains("is-match-zone")),
        wasInMatchZone: tile.classList.contains("is-match-zone"),
      },
    ]),
  );

  [playerPattern[tileIndex], playerPattern[emptyIndex]] =
    [playerPattern[emptyIndex], playerPattern[tileIndex]];
  [tiles[tileIndex], tiles[emptyIndex]] = [tiles[emptyIndex], tiles[tileIndex]];
  playerPattern.forEach((color, index) => {
    const tile = tiles[index];
    const colorName = color === EMPTY_TILE ? null : COLOR_MARKS[color].name;
    tile.dataset.index = String(index);
    tile.setAttribute(
      "aria-label",
      colorName
        ? `${colorName} tile, position ${index + 1}${MATCH_ZONE_INDICES.includes(index) ? ", matching zone" : ""}`
        : `Empty space, position ${index + 1}${MATCH_ZONE_INDICES.includes(index) ? ", matching zone" : ""}`,
    );
    tile.classList.toggle("is-match-zone", MATCH_ZONE_INDICES.includes(index));
    tile.disabled = color === EMPTY_TILE || gameOver || isTransitioning;
    playerGrid.append(tile);
  });

  if (!window.matchMedia("(prefers-reduced-motion: reduce)").matches) {
    tiles.forEach((tile) => {
      const before = oldPositions.get(tile);
      const offsetX = before.left - tile.offsetLeft;
      const offsetY = before.top - tile.offsetTop;
      const isInMatchZone = tile.classList.contains("is-match-zone");
      const afterScale = getTileFocusScale(isInMatchZone);
      const isEmptyTile = playerPattern[Number(tile.dataset.index)] === EMPTY_TILE;

      if ((offsetX !== 0 || offsetY !== 0) && !isEmptyTile) {
        // Animate position and size together, then give entering tiles a brief elastic magnetic snap.
        activeSlideAnimations.get(tile)?.cancel();
        window.clearTimeout(landingEffectTimeouts.get(tile));
        landingEffectTimeouts.delete(tile);
        tile.classList.remove("is-magnetic-land");
        tile.classList.add("is-sliding");
        const isEnteringMatchZone = !before.wasInMatchZone && isInMatchZone;
        const magneticKeyframes = isEnteringMatchZone
          ? [
            { transform: `translate(${offsetX}px, ${offsetY}px) scale(${before.scale})` },
            {
              transform: `translate(${-offsetX * 0.04}px, ${-offsetY * 0.04}px) scale(1.12)`,
              offset: 0.76,
            },
            { transform: `translate(0, 0) scale(${afterScale})` },
          ]
          : [
            { transform: `translate(${offsetX}px, ${offsetY}px) scale(${before.scale})` },
            {
              transform: `translate(${offsetX * 0.04}px, ${offsetY * 0.04}px) scale(${afterScale})`,
              offset: 0.82,
            },
            { transform: `translate(0, 0) scale(${afterScale})` },
          ];
        const animation = tile.animate(
          magneticKeyframes,
          {
            duration: SWAP_ANIMATION_MS,
            easing: isEnteringMatchZone
              ? "cubic-bezier(0.16, 0.84, 0.24, 1)"
              : "cubic-bezier(0.2, 0.8, 0.2, 1)",
          },
        );
        activeSlideAnimations.set(tile, animation);

        const clearSlideState = (landed = false) => {
          if (activeSlideAnimations.get(tile) === animation) {
            activeSlideAnimations.delete(tile);
            tile.classList.remove("is-sliding");
            if (landed && isEnteringMatchZone) {
              tile.classList.add("is-magnetic-land");
              const timeoutId = window.setTimeout(() => {
                tile.classList.remove("is-magnetic-land");
                landingEffectTimeouts.delete(tile);
              }, 560);
              landingEffectTimeouts.set(tile, timeoutId);
            }
          }
        };
        animation.addEventListener("finish", () => clearSlideState(true), { once: true });
        animation.addEventListener("cancel", () => clearSlideState(), { once: true });
      }
    });
  }
}

function showReward(isNewHighScore) {
  successParticles.replaceChildren();
  const particleColors = ["#ff5b66", "#4c9fff", "#42d6a0", "#ffd05a", "#b6adff"];

  particleColors.forEach((color, colorIndex) => {
    for (let particleIndex = 0; particleIndex < 4; particleIndex += 1) {
      const particle = document.createElement("span");
      const angle = ((colorIndex * 4 + particleIndex) / 20) * Math.PI * 2;
      const distance = 55 + ((colorIndex + particleIndex) % 3) * 22;
      particle.className = "success-particle";
      particle.style.setProperty("--particle-x", `${Math.cos(angle) * distance}px`);
      particle.style.setProperty("--particle-y", `${Math.sin(angle) * distance}px`);
      particle.style.setProperty("--particle-color", color);
      successParticles.append(particle);
    }
  });

  newHighScoreBanner.hidden = !isNewHighScore;
  successOverlay.hidden = false;
  successOverlay.classList.remove("is-visible");
  void successOverlay.offsetWidth;
  successOverlay.classList.add("is-visible");
  playerGrid.classList.add("is-success");
}

function animateScore(fromScore, toScore) {
  if (scoreAnimationFrame !== null) {
    window.cancelAnimationFrame(scoreAnimationFrame);
    scoreAnimationFrame = null;
  }

  if (window.matchMedia("(prefers-reduced-motion: reduce)").matches) {
    scoreDisplay.textContent = String(toScore);
    return;
  }

  const startTime = performance.now();
  const duration = 520;
  const updateScore = (now) => {
    const progress = Math.min((now - startTime) / duration, 1);
    const easedProgress = 1 - (1 - progress) ** 3;
    scoreDisplay.textContent = String(Math.round(fromScore + (toScore - fromScore) * easedProgress));

    if (progress < 1) {
      scoreAnimationFrame = window.requestAnimationFrame(updateScore);
    } else {
      scoreAnimationFrame = null;
    }
  };

  scoreAnimationFrame = window.requestAnimationFrame(updateScore);
}

function finishPuzzleTransition() {
  transitionTimeout = null;

  if (gameOver) {
    return;
  }

  isTransitioning = false;
  playerGrid.classList.remove("is-entering");
  targetGrid.classList.remove("is-entering");
  setTilesDisabled(false);
  gridHint.textContent = "Slide a neighboring tile into the empty space";
  setStatus("New pattern! Match the outlined center to build your score.");
}

function startNextPuzzle() {
  successOverlay.hidden = true;
  successOverlay.classList.remove("is-visible");
  playerGrid.classList.remove("is-success");
  const nextPuzzle = makePuzzle(targetPattern);
  targetPattern = nextPuzzle.target;
  playerPattern = nextPuzzle.board;
  puzzleRewarded = false;
  roundNumberDisplay.textContent = String(puzzlesCompleted + 1).padStart(2, "0");
  renderTarget();
  renderPlayerGrid();
  targetGrid.classList.add("is-entering");
  playerGrid.classList.add("is-entering");
  isTransitioning = true;
  setTilesDisabled(true);
  transitionTimeout = window.setTimeout(finishPuzzleTransition, PUZZLE_TRANSITION_MS);
}

function completePuzzle() {
  if (gameOver || puzzleRewarded) {
    return;
  }

  puzzleRewarded = true;
  puzzlesCompleted += 1;
  const previousScore = score;
  score += 100;
  remainingSeconds += 10;
  const achievedNewHighScore = score > bestScore;
  const showNewHighScoreCue = achievedNewHighScore && !newHighScoreThisRun;
  if (achievedNewHighScore) {
    bestScore = score;
    bestScoreDisplay.textContent = String(bestScore);
    saveBestScore();
  }
  if (showNewHighScoreCue) {
    newHighScoreThisRun = true;
  }
  animateScore(previousScore, score);
  puzzleCountDisplay.textContent = String(puzzlesCompleted);
  updateTimerDisplay();
  showReward(showNewHighScoreCue);
  setStatus("Pattern matched! +100 points and 10 seconds.");
  transitionTimeout = window.setTimeout(() => {
    transitionTimeout = null;
    if (!gameOver) {
      startNextPuzzle();
    }
  }, SUCCESS_ANIMATION_MS);
}

function handleTileClick(event) {
  const tile = event.target.closest(".tile");

  if (!tile || gameOver || isTransitioning) {
    return;
  }

  const clickedIndex = Number(tile.dataset.index);
  if (playerPattern[clickedIndex] === EMPTY_TILE) {
    return;
  }

  const emptyIndex = getEmptyIndex(playerPattern);
  if (!getAdjacentTileIndices(emptyIndex).includes(clickedIndex)) {
    return;
  }

  if (!timerStarted) {
    startTimer();
  }

  slideTile(clickedIndex, emptyIndex);
  const patternMatched = checkPattern();
  totalMoves += 1;
  moveCountDisplay.textContent = String(totalMoves);
  gridHint.textContent = "Slide a neighboring tile into the empty space";
  setStatus("Nice slide. Keep going!");

  if (patternMatched && !puzzleRewarded) {
    isTransitioning = true;
    setTilesDisabled(true);
    completePuzzle();
  }
}

function endGame() {
  gameOver = true;
  isTransitioning = false;
  stopTimer();
  successOverlay.hidden = true;
  successOverlay.classList.remove("is-visible");
  playerGrid.classList.remove("is-success");

  if (scoreAnimationFrame !== null) {
    window.cancelAnimationFrame(scoreAnimationFrame);
    scoreAnimationFrame = null;
    scoreDisplay.textContent = String(score);
  }

  if (transitionTimeout !== null) {
    window.clearTimeout(transitionTimeout);
    transitionTimeout = null;
  }

  playerGrid.classList.remove("is-entering");
  targetGrid.classList.remove("is-entering");
  setTilesDisabled(true);
  gridHint.textContent = "The run is over";
  setStatus("Time's up. Play again for another run!");
  finalScoreDisplay.textContent = String(score);
  finalBestScoreDisplay.textContent = String(bestScore);
  finalPuzzlesDisplay.textContent = String(puzzlesCompleted);
  finalMovesDisplay.textContent = String(totalMoves);
  personalBestBanner.hidden = !newHighScoreThisRun;
  gameOverPanel.hidden = false;
  playAgainButton.focus();
}

function startGame() {
  stopTimer();
  if (scoreAnimationFrame !== null) {
    window.cancelAnimationFrame(scoreAnimationFrame);
    scoreAnimationFrame = null;
  }
  if (transitionTimeout !== null) {
    window.clearTimeout(transitionTimeout);
    transitionTimeout = null;
  }

  totalMoves = 0;
  score = 0;
  puzzlesCompleted = 0;
  newHighScoreThisRun = false;
  remainingSeconds = STARTING_SECONDS;
  timerStarted = false;
  isTransitioning = false;
  gameOver = false;
  puzzleRewarded = false;
  const firstPuzzle = makePuzzle();
  targetPattern = firstPuzzle.target;
  playerPattern = firstPuzzle.board;

  moveCountDisplay.textContent = "0";
  scoreDisplay.textContent = "0";
  bestScoreDisplay.textContent = String(bestScore);
  puzzleCountDisplay.textContent = "0";
  roundNumberDisplay.textContent = "01";
  updateTimerDisplay();
  gameOverPanel.hidden = true;
  personalBestBanner.hidden = true;
  successOverlay.hidden = true;
  successOverlay.classList.remove("is-visible");
  newHighScoreBanner.hidden = true;
  playerGrid.classList.remove("is-success");
  gridHint.textContent = "Slide a neighboring tile into the empty space";
  setStatus("Ready when you are. Your 60 seconds start on your first slide.");
  renderTarget();
  renderPlayerGrid();
}

playerGrid.addEventListener("click", handleTileClick);
playAgainButton.addEventListener("click", startGame);
colorblindToggle.addEventListener("change", () => {
  colorblindMode = colorblindToggle.checked;
  applyColorblindMode(colorblindMode);
  saveColorblindPreference(colorblindMode);
  setStatus(`Colorblind mode ${colorblindMode ? "on" : "off"}.`);
});

colorblindMode = loadColorblindPreference();
updateTileLabels();
startGame();
