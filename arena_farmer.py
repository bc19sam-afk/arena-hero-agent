from __future__ import annotations

import argparse
import heapq
import math
import os
import socket
import sys
import threading
import time
from collections import Counter, deque
from collections.abc import Callable, Iterable, Mapping, Sequence
from dataclasses import dataclass
from enum import Enum
from getpass import getpass
from itertools import count
from pathlib import Path
from typing import Protocol
from uuid import UUID

from arena_health import write_heartbeat
from arena_hero import (
    APIError,
    ArenaHeroClient,
    ArenaHeroError,
    AuthenticationError,
    BeaconStatus,
    CommandSource,
    CoreState,
    Direction,
    PolicyViolationError,
    ProtocolError,
    Received,
    TransportError,
    Turn,
    UnitType,
    unit_cost,
)

API_KEY_ENV = "ARENA_HERO_API_KEY"
DEFAULT_BASE_URL = "https://api.arenahero.io"
DEFAULT_COMPATIBILITY_MARKER = Path(
    "/var/lib/arena-hero-version/compatibility-hold.json"
)
# The prize target is an inventory goal, not a reason to chase the Beacon.
# Keep a 10-resource capacity buffer so two Unit losses do not immediately
# reduce the Core below the 150-resource redemption threshold.
RESOURCE_REDEMPTION_TARGET = 150
RESOURCE_CAPACITY_BUFFER = 10
DEFAULT_WORKER_TARGET = 18
DEFAULT_BEACON_POLICY = "retreat"
BASE_WORKER_TARGET = 6
CORE_RESOURCE_RESERVE = 10
LATE_EXPANSION_RESERVE = 15
EARLY_DEFENSE_WORKER_GOAL = 8
EARLY_DEFENSE_RESERVE = 15
LONG_TERM_DEFENSE_RESERVE = 15
EARLY_DEFENSE_VANGUARD_TARGET = 1
EARLY_DEFENSE_RANGER_TARGET = 1
MIDGAME_WORKER_GOAL = 12
MIDGAME_VANGUARD_TARGET = 4
MIDGAME_RANGER_TARGET = 4
DEFENSE_VANGUARD_TARGET = 7
DEFENSE_RANGER_TARGET = 7
PLANNED_POPULATION_CAP = (
    (RESOURCE_REDEMPTION_TARGET + RESOURCE_CAPACITY_BUFFER + 4) // 5
)
MAX_WORKER_TARGET = (
    PLANNED_POPULATION_CAP - DEFENSE_VANGUARD_TARGET - DEFENSE_RANGER_TARGET
)
VANGUARD_GUARD_RADIUS = 3
RANGER_GUARD_RADIUS = 2
VANGUARD_CORE_GUARDS = 1
RANGER_CORE_GUARDS = 1
ISOLATED_CORE_CONFIRM_TICKS = 2
CORE_VISIBILITY_GAP_TICKS = 2
CORE_RAID_STRIKE_MAX_DISTANCE = 48
CORE_RAID_STRIKE_RELEASE_DISTANCE = 56
CORE_RAID_MEMORY_TTL = 16
CORE_RAID_STAGE_DISTANCE = 6
CORE_RAID_STAGE_TOLERANCE = 1
CORE_RAID_BREACH_READY_RADIUS = 4
CORE_RAID_SUPERIORITY_MARGIN = 3
CORE_RAID_MAX_HP_LOSS_RATIO = 0.25
CORE_RAID_NO_PROGRESS_TICKS = 10
CORE_RAID_TARGET_COOLDOWN_TICKS = 16
RAID_EPISODE_HISTORY_LIMIT = 8
CORE_RAID_REINFORCEMENT_RADIUS = 7
CORE_RAID_HOME_RESPONSE_RADIUS = 16
CORE_RAID_CUT_VANGUARDS = 1
CORE_RAID_CUT_RANGERS = 1
CORE_OBSERVER_MIN_DISTANCE = 2
CORE_OBSERVER_MAX_DISTANCE = 3
CORE_VISION_RADIUS = 5
UNIT_VISION_RADII = {
    UnitType.WORKER: 3,
    UnitType.VANGUARD: 4,
    UnitType.RANGER: 5,
}
ISOLATED_CORE_MIN_RESOURCES = 5
ISOLATED_CORE_MIN_RESOURCE_SPACE = 10
STATIC_WORKER_CONFIRM_TICKS = 2
STATIC_WORKER_CLEAR_MAX_DISTANCE = 16
STATIC_WORKER_CLEAR_VANGUARDS = 2
STATIC_WORKER_CLEAR_RANGERS = 2
CORE_PROTECTOR_RADIUS = 5
UNIT_HEAL_RESOURCE_RESERVE = 10
POST_THREAT_CAUTION_TICKS = 8
RECENT_ATTACK_MEMORY_TICKS = 6
PURSUIT_MEMORY_TTL = 2
PURSUIT_SCORE_MAX = 4
DISTANT_PURSUIT_SCORE_THRESHOLD = 3
PREDICTION_MIN_OBSERVATIONS = 2
ACTIVE_ENEMY_ALERT_TICKS = 2
CORE_PREEMPTIVE_EVADE_HORIZON_TICKS = 16
SQUAD_DISENGAGE_TICKS = 8
SCOUT_SAFE_RETURN_RADIUS = 3
SCOUT_COOLDOWN_TICKS = 3
STATIONARY_CORE_MEMORY_TTL = 256
RESOURCE_MEMORY_TTL = 64
RESOURCE_STALL_TICKS = 6
RESOURCE_COOLDOWN_TICKS = 8
RESOURCE_ASSIGNMENT_STICKY_BONUS = 2
SCOUT_STALL_TICKS = 3
SCOUT_RETURN_HISTORY_PENALTY = 16
RECOVERY_TICKS = 160
RECOVERY_VANGUARD_WORKER_GOAL = 4
RECOVERY_MIN_WORKERS = 6
RECOVERY_RANGER_WORKER_GOAL = RECOVERY_MIN_WORKERS
RECOVERY_MIN_RESOURCES = 20
RECOVERY_THREAT_DISTANCE = 12
RECOVERY_INFERENCE_RESOURCE_LIMIT = CORE_RESOURCE_RESERVE + unit_cost(
    UnitType.WORKER,
    0,
)
LOG_SNAPSHOT_INTERVAL = 20
PATH_COST_MAX_EXPANSIONS = 512
PATH_COST_UNREACHABLE = 1_000_000
CORE_SHORT_CARGO_ETA = 2
CORE_BULK_CARGO_ETA = 4
CORE_BULK_CARGO = 3
CORE_CONGESTED_CARGO = 3
CORE_DELIVERY_CHAIN_MAX = 8
CORE_EVADE_TRIGGER_DISTANCE = 12
CORE_EVADE_RELEASE_DISTANCE = CORE_EVADE_TRIGGER_DISTANCE + 2
CORE_MOVE_COMMIT_PROGRESS = 2
UNIT_EVADE_TRIGGER_DISTANCE = 5
RETREAT_MIN_BEACON_DISTANCE = 224
RETREAT_SERVICE_TICKS = 8
SIGNED_INT64_MIN = -(2**63)
SIGNED_INT64_MAX = 2**63 - 1
TRANSIENT_EXIT_CODE = 75
CONFIGURATION_EXIT_CODE = 2
AUTHENTICATION_EXIT_CODE = 10
POLICY_EXIT_CODE = 11
PROTOCOL_EXIT_CODE = 12
API_EXIT_CODE = 13
AGENT_EXIT_CODE = 14
DEFAULT_STALE_TURN_TIMEOUT_SECONDS = 0.0
TURN_SKIP_API_ERRORS = frozenset(
    {
        "COMMAND_RATE_LIMITED",
        "COMMAND_WINDOW_CLOSED",
        "TICK_MISMATCH",
        "TICK_NOT_READY",
    }
)
CARDINAL_DIRECTIONS = (
    Direction.UP,
    Direction.RIGHT,
    Direction.DOWN,
    Direction.LEFT,
)
RANGER_LINE_VECTORS = (
    (0, -1),
    (1, -1),
    (1, 0),
    (1, 1),
    (0, 1),
    (-1, 1),
    (-1, 0),
    (-1, -1),
)
# A worker's vision radius is three cells.  Six horizontal/vertical lanes with
# at most six cells between them cover every cell in a 32x32 chunk while still
# leaving enough room for obstacle detours.  Each pair of points makes a full
# lane crossing; alternating the direction prevents the old radial waypoint
# plan from repeatedly walking the same narrow rays.
SCOUT_SCAN_WAYPOINTS = (
    (2, 2),
    (29, 2),
    (29, 8),
    (2, 8),
    (2, 14),
    (29, 14),
    (29, 20),
    (2, 20),
    (2, 26),
    (29, 26),
    (29, 31),
    (2, 31),
)
SCOUT_STAGE_CYCLE = len(SCOUT_SCAN_WAYPOINTS)
SCOUT_CHUNK_SEARCH_RADIUS = 4
SCOUT_CHUNK_OFFSETS = tuple(
    sorted(
        (
            (dx, dy)
            for dx in range(-SCOUT_CHUNK_SEARCH_RADIUS, SCOUT_CHUNK_SEARCH_RADIUS + 1)
            for dy in range(-SCOUT_CHUNK_SEARCH_RADIUS, SCOUT_CHUNK_SEARCH_RADIUS + 1)
        ),
        key=lambda offset: (
            abs(offset[0]) + abs(offset[1]),
            max(abs(offset[0]), abs(offset[1])),
            offset[0],
            offset[1],
        ),
    )
)
SCOUT_COVERAGE_MEMORY_TTL = 4096

Position = tuple[int, int]


class LifecycleMode(str, Enum):
    ACTIVE = "ACTIVE"
    RESPAWNING = "RESPAWNING"
    COMPATIBILITY_HOLD = "COMPATIBILITY_HOLD"
    RECOVERY = "RECOVERY"


class ThreatLevel(str, Enum):
    NORMAL = "NORMAL"
    ALERT = "ALERT"
    PRE_EVADE = "PRE_EVADE"
    ENGAGED = "ENGAGED"
    BREAKOUT = "BREAKOUT"


class GlobalPosture(str, Enum):
    NORMAL = "NORMAL"
    ALERT = "ALERT"
    PRE_EVADE = "PRE_EVADE"
    ENGAGED = "ENGAGED"
    BREAKOUT = "BREAKOUT"
    RECOVERY = "RECOVERY"
    COMPATIBILITY_HOLD = "COMPATIBILITY_HOLD"
    RESPAWNING = "RESPAWNING"


class RaidPhase(str, Enum):
    PROBE = "PROBE"
    STAGE = "STAGE"
    BREACH = "BREACH"
    CORE_FOCUS = "CORE_FOCUS"
    ABORT = "ABORT"
    RECOVER = "RECOVER"


class RaidMode(str, Enum):
    CUT = "CUT"
    SIEGE = "SIEGE"


def _chunk_coordinates(position: Position) -> Position:
    return position[0] // 32, position[1] // 32


def _chunk_axis(value: int) -> int:
    return value if value >= 0 else -value - 1


def _chunk_resource_quota(position: Position) -> int:
    chunk_x, chunk_y = _chunk_coordinates(position)
    ring = _chunk_axis(chunk_x) + _chunk_axis(chunk_y)
    return max(2, (16 * 8) // (8 + ring))


class Movable(Protocol):
    id: object
    position: Position

    def move(self, direction: Direction) -> None: ...


@dataclass(slots=True)
class MovementContext:
    obstacles: set[Position]
    resource_cells: set[Position]
    enemy_cells: set[Position]
    danger_cells: set[Position]
    discouraged_cells: set[Position]
    friendly_counts: Counter[Position]
    reserved_destinations: set[Position]
    core_position: Position | None
    delivery_lane: Position | None = None
    preplanned_units: set[UUID] | None = None


@dataclass(slots=True)
class ResourceProgress:
    target: Position
    best_cost: int
    stalled_turns: int = 0


@dataclass(slots=True)
class ScoutProgress:
    target: Position
    best_cost: int
    stalled_turns: int = 0


@dataclass(slots=True)
class EnemyCoreSighting:
    position: Position
    first_tick: int
    last_tick: int
    observations: int = 1


@dataclass(slots=True, frozen=True)
class CoreRaidTarget:
    id: UUID
    position: Position
    visible_enemy: object | None


@dataclass(slots=True)
class RaidEpisode:
    target_id: UUID
    mode: RaidMode
    start_tick: int
    start_resources: int
    start_vanguard_count: int
    start_ranger_count: int
    initial_member_ids: frozenset[UUID]
    initial_member_hp: int
    initial_defender_count: int
    initial_target_durability: int | None
    rebuild_vanguard_target: int
    rebuild_ranger_target: int
    spotter_id: UUID | None = None
    outcome: str = "ACTIVE"
    engagement_end_tick: int | None = None
    engagement_end_resources: int | None = None
    last_target_durability: int | None = None
    surviving_member_ids: frozenset[UUID] = frozenset()
    return_member_ids: frozenset[UUID] = frozenset()
    return_spotter_ids: frozenset[UUID] = frozenset()
    squad_return_complete_tick: int | None = None
    scout_return_complete_tick: int | None = None
    rebuild_complete_tick: int | None = None
    ready_tick: int | None = None
    ready_resources: int | None = None
    ready_vanguard_count: int | None = None
    ready_ranger_count: int | None = None
    cycle_end_reason: str = "PENDING"

    @property
    def state(self) -> str:
        if self.engagement_end_tick is None:
            return "ENGAGED"
        if (
            self.squad_return_complete_tick is None
            or self.scout_return_complete_tick is None
        ):
            return "RETURNING"
        if self.rebuild_complete_tick is None:
            return "REBUILDING"
        if self.ready_tick is None:
            return "FINALIZING"
        return "READY"

    @property
    def loss_count(self) -> int:
        return len(self.initial_member_ids - self.surviving_member_ids)

    @property
    def engagement_duration(self) -> int | None:
        if self.engagement_end_tick is None:
            return None
        return self.engagement_end_tick - self.start_tick

    @property
    def recovery_duration(self) -> int | None:
        if self.engagement_end_tick is None or self.ready_tick is None:
            return None
        return self.ready_tick - self.engagement_end_tick

    @property
    def total_duration(self) -> int | None:
        if self.ready_tick is None:
            return None
        return self.ready_tick - self.start_tick


@dataclass(slots=True)
class EnemyUnitMotion:
    position: Position
    last_tick: int
    core_distance: int
    unit_type: UnitType
    movement_delta: Position | None = None
    movement_observations: int = 0
    pursuit_score: int = 0
    pursuit_ticks: int = 0
    activity_until_tick: int = 0
    preemptive_evade_until_tick: int = 0
    ticks_to_attack_range: int | None = None


@dataclass(slots=True, frozen=True)
class RememberedThreat:
    id: UUID
    position: Position
    unit_type: UnitType
    expires_tick: int


@dataclass(slots=True, frozen=True)
class ThreatAssessment:
    lifecycle: LifecycleMode = LifecycleMode.ACTIVE
    level: ThreatLevel = ThreatLevel.NORMAL
    primary_reason: str = "NONE"
    recent_attack: bool = False
    recent_core_attack: bool = False
    activity_enemy_ids: frozenset[UUID] = frozenset()
    preemptive_enemy_ids: frozenset[UUID] = frozenset()
    pursuing_enemy_ids: frozenset[UUID] = frozenset()
    near_core_enemy_ids: frozenset[UUID] = frozenset()
    threatening_core_enemy_ids: frozenset[UUID] = frozenset()
    disengaging: bool = False
    local_squad_contact: bool = False
    caution: bool = False
    breakout: bool = False

    @property
    def combat_pressure(self) -> bool:
        return bool(
            self.recent_attack
            or self.disengaging
            or self.activity_enemy_ids
            or self.pursuing_enemy_ids
            or self.near_core_enemy_ids
            or self.local_squad_contact
        )

    @property
    def global_posture(self) -> GlobalPosture:
        if self.lifecycle is LifecycleMode.RESPAWNING:
            return GlobalPosture.RESPAWNING
        if self.lifecycle is LifecycleMode.COMPATIBILITY_HOLD:
            return GlobalPosture.COMPATIBILITY_HOLD
        if self.lifecycle is LifecycleMode.RECOVERY:
            return GlobalPosture.RECOVERY
        return GlobalPosture(self.level.value)


@dataclass(slots=True, frozen=True)
class ResourceLedgerSnapshot:
    tick: int
    resources: int
    population: int
    workers: int
    vanguards: int
    rangers: int
    actions: str
    core_action: str


@dataclass(slots=True, frozen=True)
class ResourceLedgerResult:
    previous: ResourceLedgerSnapshot
    tick: int
    resources: int
    population: int
    workers: int
    vanguards: int
    rangers: int
    actual_delta: int
    expected_delta: int
    unexplained_delta: int
    events: str
    skipped_reason: str | None = None

    @property
    def unexplained_loss(self) -> int:
        return max(0, -self.unexplained_delta)


def _api_key_from_env_file(path: Path) -> str | None:
    for raw_line in path.read_text(encoding="utf-8-sig").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("export "):
            line = line.removeprefix("export ").lstrip()
        name, separator, value = line.partition("=")
        if separator and name.strip() == API_KEY_ENV:
            value = value.strip()
            if len(value) >= 2 and value[0] == value[-1] and value[0] in {'"', "'"}:
                value = value[1:-1]
            return value or None
    return None


def load_api_key(
    *,
    env_file: Path | None = None,
    can_prompt: bool | None = None,
    prompt: Callable[[str], str] | None = None,
) -> str:
    if key := os.environ.get(API_KEY_ENV, "").strip():
        return key

    selected_env_file = env_file or Path.cwd() / ".env"
    if selected_env_file.is_file():
        if key := _api_key_from_env_file(selected_env_file):
            return key
        if env_file is not None:
            raise ValueError(f"{API_KEY_ENV} is missing from {selected_env_file}")
    elif env_file is not None:
        raise ValueError(f"Environment file does not exist: {selected_env_file}")

    if can_prompt is None:
        can_prompt = sys.stdin.isatty()
    if not can_prompt:
        raise ValueError(f"Set {API_KEY_ENV} or add it to .env")

    key = (prompt or getpass)("Arena Hero API key: ").strip()
    if not key:
        raise ValueError("API key cannot be empty")
    return key


def _distance(left: Position, right: Position) -> int:
    return abs(left[0] - right[0]) + abs(left[1] - right[1])


def _core_raid_strike_distance(
    position: Position,
    vanguards: Sequence[object],
    rangers: Sequence[object],
) -> int:
    return max(
        min(_distance(defender.position, position) for defender in vanguards),
        min(_distance(defender.position, position) for defender in rangers),
    )


def _minimum_cost_assignment(costs: Sequence[Sequence[int]]) -> tuple[int, ...]:
    """Return one deterministic minimum-cost column for each matrix row."""
    if not costs:
        return ()
    row_count = len(costs)
    column_count = len(costs[0])
    if column_count < row_count or any(
        len(row) != column_count for row in costs
    ):
        raise ValueError("assignment matrix must be rectangular with rows <= columns")

    row_potential = [0] * (row_count + 1)
    column_potential = [0] * (column_count + 1)
    matched_row = [0] * (column_count + 1)
    previous_column = [0] * (column_count + 1)

    for row_index in range(1, row_count + 1):
        matched_row[0] = row_index
        current_column = 0
        minimum_slack = [sys.maxsize] * (column_count + 1)
        visited = [False] * (column_count + 1)
        while True:
            visited[current_column] = True
            current_row = matched_row[current_column]
            delta = sys.maxsize
            next_column = 0
            for column_index in range(1, column_count + 1):
                if visited[column_index]:
                    continue
                reduced_cost = (
                    costs[current_row - 1][column_index - 1]
                    - row_potential[current_row]
                    - column_potential[column_index]
                )
                if reduced_cost < minimum_slack[column_index]:
                    minimum_slack[column_index] = reduced_cost
                    previous_column[column_index] = current_column
                if minimum_slack[column_index] < delta:
                    delta = minimum_slack[column_index]
                    next_column = column_index
            for column_index in range(column_count + 1):
                if visited[column_index]:
                    row_potential[matched_row[column_index]] += delta
                    column_potential[column_index] -= delta
                else:
                    minimum_slack[column_index] -= delta
            current_column = next_column
            if matched_row[current_column] == 0:
                break
        while True:
            next_column = previous_column[current_column]
            matched_row[current_column] = matched_row[next_column]
            current_column = next_column
            if current_column == 0:
                break

    assignment = [-1] * row_count
    for column_index in range(1, column_count + 1):
        row_index = matched_row[column_index]
        if row_index:
            assignment[row_index - 1] = column_index - 1
    return tuple(assignment)


def _destination(position: Position, direction: Direction) -> Position:
    dx, dy = direction.delta
    return position[0] + dx, position[1] + dy


def _is_signed_int64_position(position: Position) -> bool:
    return all(
        SIGNED_INT64_MIN <= coordinate <= SIGNED_INT64_MAX
        for coordinate in position
    )


def _minimum_enemy_distance(
    position: Position,
    enemies: Sequence[object],
) -> int:
    return min(
        (_distance(position, enemy.position) for enemy in enemies),
        default=SIGNED_INT64_MAX,
    )


def _enemy_distance_vector(
    position: Position,
    enemies: Sequence[object],
) -> tuple[int, ...]:
    return tuple(sorted(_distance(position, enemy.position) for enemy in enemies))


def _position_threat_key(
    position: Position,
    enemies: Sequence[object],
    obstacles: set[Position],
) -> tuple[int, tuple[int, ...]]:
    distances = _enemy_distance_vector(position, enemies)
    return (
        _projected_core_damage(position, enemies, obstacles),
        tuple(-distance for distance in distances),
    )


def _retreat_direction(
    position: Position,
    beacon_position: Position,
    enemies: Sequence[object],
    obstacles: set[Position],
    blocked: set[Position],
    previous_direction: Direction | None,
    *,
    allow_beacon_approach: bool,
) -> Direction | None:
    current_beacon_distance = _distance(position, beacon_position)
    away_vector = (
        position[0] - beacon_position[0],
        position[1] - beacon_position[1],
    )
    candidates: list[tuple[tuple[object, ...], Direction]] = []
    for index, direction in enumerate(CARDINAL_DIRECTIONS):
        destination = _destination(position, direction)
        if destination in blocked or not _is_signed_int64_position(destination):
            continue
        beacon_distance = _distance(destination, beacon_position)
        if beacon_distance < current_beacon_distance and not allow_beacon_approach:
            continue
        dx, dy = direction.delta
        alignment = dx * away_vector[0] + dy * away_vector[1]
        continuity = int(direction is previous_direction)
        if enemies:
            score = (
                *_position_threat_key(destination, enemies, obstacles),
                -beacon_distance,
                -alignment,
                -continuity,
                index,
            )
        else:
            score = (
                -beacon_distance,
                -alignment,
                -continuity,
                index,
            )
        candidates.append((score, direction))
    if not candidates:
        return None
    best_score, best_direction = min(candidates, key=lambda candidate: candidate[0])
    if (
        enemies
        and best_score[0]
        > _projected_core_damage(position, enemies, obstacles)
    ):
        return None
    return best_direction


def _threat_axis(origin: Position, target: Position) -> Direction:
    dx = target[0] - origin[0]
    dy = target[1] - origin[1]
    if abs(dx) >= abs(dy):
        return Direction.RIGHT if dx >= 0 else Direction.LEFT
    return Direction.DOWN if dy >= 0 else Direction.UP


def _is_multi_axis_breakout(
    position: Position,
    enemies: Sequence[object],
    obstacles: set[Position],
    blocked: set[Position],
) -> bool:
    if len(enemies) < 2 or _projected_core_damage(position, enemies, obstacles) == 0:
        return False
    if len({_threat_axis(position, enemy.position) for enemy in enemies}) < 2:
        return False

    current_distances = {
        enemy.id: _distance(position, enemy.position) for enemy in enemies
    }
    for direction in CARDINAL_DIRECTIONS:
        destination = _destination(position, direction)
        if destination in blocked or not _is_signed_int64_position(destination):
            continue
        if all(
            _distance(destination, enemy.position) > current_distances[enemy.id]
            for enemy in enemies
        ):
            return False
    return True


def _directions_toward(start: Position, target: Position) -> tuple[Direction, ...]:
    ranked = sorted(
        CARDINAL_DIRECTIONS,
        key=lambda direction: (
            _distance(_destination(start, direction), target),
            CARDINAL_DIRECTIONS.index(direction),
        ),
    )
    return tuple(ranked)


def _path_directions(
    start: Position,
    target: Position,
    blocked: set[Position],
    *,
    discouraged: set[Position] | None = None,
    discouraged_penalty: int = 4,
    max_expansions: int = 4096,
) -> tuple[Direction, ...]:
    if start == target:
        return ()

    blocked = set(blocked)
    blocked.discard(start)
    discouraged = set(discouraged or ())
    discouraged.discard(start)
    goals = {target}
    if target in blocked:
        goals = {
            _destination(target, direction)
            for direction in CARDINAL_DIRECTIONS
            if _destination(target, direction) not in blocked
        }
    if not goals or start in goals:
        return ()

    def distance_to_goal(position: Position) -> int:
        return min(_distance(position, goal) for goal in goals)

    sequence = count()
    start_distance = distance_to_goal(start)
    frontier: list[tuple[int, int, int, int, Position]] = [
        (start_distance, start_distance, 0, next(sequence), start)
    ]
    costs = {start: 0}
    came_from: dict[Position, tuple[Position, Direction]] = {}
    expansions = 0
    reached: Position | None = None

    while frontier and expansions < max_expansions:
        _, _, current_cost, _, current = heapq.heappop(frontier)
        if current_cost != costs.get(current):
            continue
        if current in goals:
            reached = current
            break

        expansions += 1
        for direction in CARDINAL_DIRECTIONS:
            destination = _destination(current, direction)
            if destination in blocked:
                continue
            new_cost = current_cost + 1
            if destination in discouraged:
                new_cost += discouraged_penalty
            if new_cost >= costs.get(destination, sys.maxsize):
                continue
            costs[destination] = new_cost
            came_from[destination] = (current, direction)
            remaining_distance = distance_to_goal(destination)
            heapq.heappush(
                frontier,
                (
                    new_cost + remaining_distance,
                    remaining_distance,
                    new_cost,
                    next(sequence),
                    destination,
                ),
            )

    if reached is None:
        reached = min(
            came_from,
            key=lambda position: (
                distance_to_goal(position),
                costs[position],
            ),
            default=None,
        )
        if reached is None:
            return ()

    current = reached
    while True:
        previous, direction = came_from[current]
        if previous == start:
            return (direction,)
        current = previous


def _estimated_path_cost(
    start: Position,
    target: Position,
    blocked: set[Position],
    *,
    max_expansions: int = PATH_COST_MAX_EXPANSIONS,
) -> int:
    if start == target:
        return 0

    blocked = set(blocked)
    blocked.discard(start)
    if target in blocked:
        return PATH_COST_UNREACHABLE

    sequence = count()
    start_distance = _distance(start, target)
    frontier: list[tuple[int, int, int, int, Position]] = [
        (start_distance, start_distance, 0, next(sequence), start)
    ]
    costs = {start: 0}
    expansions = 0

    while frontier and expansions < max_expansions:
        _, _, current_cost, _, current = heapq.heappop(frontier)
        if current_cost != costs.get(current):
            continue
        if current == target:
            return current_cost

        expansions += 1
        for direction in CARDINAL_DIRECTIONS:
            destination = _destination(current, direction)
            if destination in blocked:
                continue
            new_cost = current_cost + 1
            if new_cost >= costs.get(destination, sys.maxsize):
                continue
            costs[destination] = new_cost
            remaining_distance = _distance(destination, target)
            heapq.heappush(
                frontier,
                (
                    new_cost + remaining_distance,
                    remaining_distance,
                    new_cost,
                    next(sequence),
                    destination,
                ),
            )

    if not frontier:
        return PATH_COST_UNREACHABLE
    return min(estimated_cost for estimated_cost, *_ in frontier)


def _exploration_directions(unit: Movable) -> tuple[Direction, ...]:
    unit_number = getattr(unit.id, "int", 0)
    offset = unit_number % len(CARDINAL_DIRECTIONS)
    return CARDINAL_DIRECTIONS[offset:] + CARDINAL_DIRECTIONS[:offset]


def _rotate_directions(
    directions: tuple[Direction, ...],
    offset: int,
) -> tuple[Direction, ...]:
    offset %= len(directions)
    return directions[offset:] + directions[:offset]


def _queue_move(
    unit: Movable,
    directions: Iterable[Direction],
    context: MovementContext,
    *,
    allow_core_entry: bool = False,
    allow_friendly_entry: Position | None = None,
    allow_single_friendly_transit: bool = False,
    avoid_danger: bool = True,
) -> bool:
    for direction in directions:
        destination = _destination(unit.position, direction)
        if destination in context.obstacles or destination in context.enemy_cells:
            continue
        if avoid_danger and destination in context.danger_cells:
            continue
        if destination in context.reserved_destinations:
            continue

        occupants = context.friendly_counts[destination]
        if occupants:
            entering_core = allow_core_entry and destination == context.core_position
            entering_allowed_friendly = destination == allow_friendly_entry
            entering_single_friendly = (
                allow_single_friendly_transit and occupants < 2
            )
            if not (
                entering_core
                or entering_allowed_friendly
                or entering_single_friendly
            ) or occupants >= 2:
                continue

        unit.move(direction)
        context.friendly_counts[unit.position] -= 1
        context.friendly_counts[destination] += 1
        context.reserved_destinations.add(destination)
        return True
    return False


def _queue_away_from_enemies(
    unit: Movable,
    enemies: Sequence[object],
    context: MovementContext,
    beacon_position: Position,
    *,
    trigger_distance: int = UNIT_EVADE_TRIGGER_DISTANCE,
    keep_core_neighbors_clear: bool = False,
) -> bool:
    """Prefer escape over work or combat whenever a visible enemy is nearby."""
    current_enemy_distance = _minimum_enemy_distance(unit.position, enemies)
    if not enemies or current_enemy_distance > trigger_distance:
        return False

    core_neighbors = set()
    if keep_core_neighbors_clear and context.core_position is not None:
        core_neighbors = {
            _destination(context.core_position, direction)
            for direction in CARDINAL_DIRECTIONS
        }

    candidates: list[tuple[tuple[object, ...], Direction]] = []
    for index, direction in enumerate(CARDINAL_DIRECTIONS):
        destination = _destination(unit.position, direction)
        if (
            destination in core_neighbors
            and unit.position != context.core_position
        ):
            continue
        candidates.append(
            (
                (
                    *_position_threat_key(
                        destination,
                        enemies,
                        context.obstacles,
                    ),
                    -_distance(destination, beacon_position),
                    index,
                ),
                direction,
            )
        )

    directions = tuple(
        direction for _, direction in sorted(candidates)
    )
    return _queue_move(
        unit,
        directions,
        context,
        avoid_danger=False,
    )


def _select_delivery_lane(context: MovementContext) -> Position | None:
    """Keep one passable Core neighbor available for cargo handoff."""
    if context.core_position is None:
        return None
    candidates: list[tuple[int, int, Position]] = []
    for index, direction in enumerate(CARDINAL_DIRECTIONS):
        destination = _destination(context.core_position, direction)
        if not _is_signed_int64_position(destination):
            continue
        if destination in context.obstacles:
            continue
        if destination in context.enemy_cells or destination in context.danger_cells:
            continue
        candidates.append(
            (int(context.friendly_counts[destination] > 0), index, destination)
        )
    return min(candidates, default=(0, 0, None))[2]


def _queue_core_defender_egress(
    turn: Turn,
    context: MovementContext,
    enemies: Sequence[object],
    healing_holds: set[UUID] | None = None,
) -> set[UUID]:
    """Move a defender off the Core before Workers plan their deliveries."""
    core = turn.core
    if core is None or context.core_position is None:
        return set()

    defenders = sorted(
        (
            defender
            for defender in (*turn.vanguards, *turn.rangers)
            if defender.position == core.position
        ),
        key=_uuid_sort_key,
    )
    if not defenders:
        return set()

    defender = defenders[0]
    core_threats = _core_threatening_enemies(
        core.position,
        enemies,
        context.obstacles,
    )
    can_counter_core_threat = any(
        (
            defender.unit_type is UnitType.VANGUARD
            and _distance(defender.position, enemy.position) == 1
        )
        or (
            defender.unit_type is UnitType.RANGER
            and _ranger_can_shoot(
                defender.position,
                enemy.position,
                context.obstacles,
            )
        )
        for enemy in core_threats
    )
    if can_counter_core_threat:
        return set()

    imminent_cargo = any(
        worker.cargo > 0
        and _distance(worker.position, core.position) <= CORE_SHORT_CARGO_ETA
        for worker in turn.workers
    )
    missing_hp = _unit_max_hp(defender.unit_type) - defender.hp
    if (
        healing_holds is not None
        and defender.id in healing_holds
        and missing_hp > 0
        and not imminent_cargo
        and core.view.state is CoreState.NORMAL
        and core.hp == 5
        and turn.resources >= UNIT_HEAL_RESOURCE_RESERVE + missing_hp
    ):
        return set()

    current_enemy_distance = _minimum_enemy_distance(defender.position, enemies)
    candidates: list[tuple[tuple[int, int, int, int], Direction]] = []
    for index, direction in enumerate(CARDINAL_DIRECTIONS):
        destination = _destination(defender.position, direction)
        if not _is_signed_int64_position(destination):
            continue
        if destination in context.obstacles:
            continue
        if destination in context.enemy_cells or destination in context.danger_cells:
            continue
        if destination in context.reserved_destinations:
            continue
        if context.friendly_counts[destination] >= 2:
            continue

        enemy_distance = _minimum_enemy_distance(destination, enemies)
        if (
            enemies
            and current_enemy_distance <= UNIT_EVADE_TRIGGER_DISTANCE
            and enemy_distance < current_enemy_distance
        ):
            continue
        candidates.append(
            (
                (
                    int(destination != context.delivery_lane),
                    enemy_distance,
                    _distance(destination, turn.beacon.position),
                    -index,
                ),
                direction,
            )
        )

    directions = tuple(
        direction for _, direction in sorted(candidates, reverse=True)
    )
    if not _queue_move(
        defender,
        directions,
        context,
        allow_single_friendly_transit=True,
    ):
        return set()
    return {defender.id}


def _queue_core_delivery_handoff(
    turn: Turn,
    context: MovementContext,
) -> set[UUID]:
    """Break a full Core cell by shifting a friendly corridor from outside in."""
    core = turn.core
    if core is None or context.core_position is None:
        return set()
    empty_workers = sorted(
        (
            worker
            for worker in turn.workers
            if worker.cargo == 0 and worker.position == core.position
        ),
        key=_uuid_sort_key,
    )
    if not empty_workers:
        return set()

    empty_worker = empty_workers[0]
    passable_neighbors = []
    for direction in CARDINAL_DIRECTIONS:
        destination = _destination(core.position, direction)
        if not _is_signed_int64_position(destination):
            continue
        if destination in context.obstacles:
            continue
        if destination in context.enemy_cells or destination in context.danger_cells:
            continue
        passable_neighbors.append((direction, destination))
    if not passable_neighbors or any(
        context.friendly_counts[position] == 0
        for _, position in passable_neighbors
    ):
        # Normal resource/scout routing clears a free lane without overriding
        # useful work. Coordination is needed only when all exits are occupied.
        return set()

    units_by_position = {
        unit.position: unit
        for unit in turn.units
        if context.friendly_counts[unit.position] == 1
    }
    starts = sorted(
        (
            (position, units_by_position.get(position), index)
            for index, (_, position) in enumerate(passable_neighbors)
            if context.friendly_counts[position] == 1
            and position in units_by_position
        ),
        key=lambda item: (
            int(getattr(item[1], "cargo", 0) > 0),
            item[2],
        ),
    )
    chain: tuple[Position, ...] | None = None
    for start, _, _ in starts:
        frontier: deque[tuple[Position, tuple[Position, ...]]] = deque(
            [(start, (start,))]
        )
        visited = {core.position, start}
        while frontier:
            current, path = frontier.popleft()
            if len(path) >= CORE_DELIVERY_CHAIN_MAX:
                continue
            for direction in CARDINAL_DIRECTIONS:
                destination = _destination(current, direction)
                if destination in visited or not _is_signed_int64_position(destination):
                    continue
                if destination in context.obstacles:
                    continue
                if destination in context.enemy_cells or destination in context.danger_cells:
                    continue
                if destination in context.reserved_destinations:
                    continue
                occupants = context.friendly_counts[destination]
                if occupants == 0:
                    chain = (*path, destination)
                    frontier.clear()
                    break
                if occupants != 1 or destination not in units_by_position:
                    continue
                visited.add(destination)
                frontier.append((destination, (*path, destination)))
            if chain is not None:
                break
        if chain is not None:
            break
    if chain is None:
        return set()

    handoff: set[UUID] = set()
    for source, destination in reversed(tuple(zip(chain[:-1], chain[1:]))):
        unit = units_by_position[source]
        direction = _direction_to_adjacent(source, destination)
        if direction is None or not _queue_move(unit, (direction,), context):
            return handoff
        handoff.add(unit.id)

    first_position = chain[0]
    first_direction = _direction_to_adjacent(core.position, first_position)
    if first_direction is None or not _queue_move(
        empty_worker,
        (first_direction,),
        context,
    ):
        return handoff
    handoff.add(empty_worker.id)

    for worker in sorted(
        (
            worker
            for worker in turn.workers
            if worker.cargo > 0
            and worker.id not in handoff
            and _distance(worker.position, core.position) == 1
        ),
        key=_uuid_sort_key,
    ):
        direction = _direction_to_adjacent(worker.position, core.position)
        if direction is not None and _queue_move(
            worker,
            (direction,),
            context,
            allow_core_entry=True,
        ):
            handoff.add(worker.id)
            break
    return handoff


def _queue_toward(
    unit: Movable,
    target: Position,
    context: MovementContext,
    *,
    allow_core_entry: bool = False,
    allow_target_entry: bool = False,
    allow_single_friendly_transit: bool = False,
    discouraged: set[Position] | None = None,
    discouraged_penalty: int = 4,
    avoid_danger: bool = True,
) -> bool:
    blocked = (
        set(context.obstacles)
        | set(context.enemy_cells)
        | set(context.reserved_destinations)
    )
    if avoid_danger:
        blocked.update(context.danger_cells)
    for cell, occupants in context.friendly_counts.items():
        if occupants <= 0 or cell == unit.position:
            continue
        entering_core = (
            allow_core_entry
            and cell == context.core_position
            and occupants < 2
        )
        entering_target = allow_target_entry and cell == target and occupants < 2
        entering_single_friendly = (
            allow_single_friendly_transit and occupants < 2
        )
        if not entering_core and not entering_target and not entering_single_friendly:
            blocked.add(cell)

    combined_discouraged = set(context.discouraged_cells)
    combined_discouraged.update(discouraged or ())
    directions = _path_directions(
        unit.position,
        target,
        blocked,
        discouraged=combined_discouraged,
        discouraged_penalty=discouraged_penalty,
    )
    if not directions:
        return False
    return _queue_move(
        unit,
        directions,
        context,
        allow_core_entry=allow_core_entry,
        allow_friendly_entry=target if allow_target_entry else None,
        allow_single_friendly_transit=allow_single_friendly_transit,
        avoid_danger=avoid_danger,
    )


def _direction_to_adjacent(start: Position, target: Position) -> Direction | None:
    delta = target[0] - start[0], target[1] - start[1]
    for direction in CARDINAL_DIRECTIONS:
        if direction.delta == delta:
            return direction
    return None


def _intermediate_cells(start: Position, target: Position) -> tuple[Position, ...]:
    dx = target[0] - start[0]
    dy = target[1] - start[1]
    distance = max(abs(dx), abs(dy))
    if distance == 0:
        return ()
    if dx != 0 and dy != 0 and abs(dx) != abs(dy):
        return ()
    step_x = 0 if dx == 0 else (1 if dx > 0 else -1)
    step_y = 0 if dy == 0 else (1 if dy > 0 else -1)
    return tuple(
        (start[0] + step_x * step, start[1] + step_y * step)
        for step in range(1, distance)
    )


def _supercover_cells(start: Position, target: Position) -> tuple[Position, ...]:
    dx = target[0] - start[0]
    dy = target[1] - start[1]
    steps_x = abs(dx)
    steps_y = abs(dy)
    if steps_x == 0 and steps_y == 0:
        return ()
    step_x = 0 if dx == 0 else (1 if dx > 0 else -1)
    step_y = 0 if dy == 0 else (1 if dy > 0 else -1)
    x, y = start
    progress_x = 0
    progress_y = 0
    cells: list[Position] = []
    while progress_x < steps_x or progress_y < steps_y:
        cross_x = (1 + 2 * progress_x) * steps_y
        cross_y = (1 + 2 * progress_y) * steps_x
        if cross_x == cross_y:
            side_x = (x + step_x, y)
            side_y = (x, y + step_y)
            if side_x != start:
                cells.append(side_x)
            if side_y != start and side_y != side_x:
                cells.append(side_y)
            x += step_x
            y += step_y
            progress_x += 1
            progress_y += 1
            diagonal = (x, y)
            if diagonal not in {side_x, side_y}:
                cells.append(diagonal)
        elif cross_x < cross_y:
            x += step_x
            progress_x += 1
            cells.append((x, y))
        else:
            y += step_y
            progress_y += 1
            cells.append((x, y))
    return tuple(cells)


def _has_vision_line(
    start: Position,
    target: Position,
    obstacles: set[Position],
) -> bool:
    return not any(
        cell != target and cell in obstacles
        for cell in _supercover_cells(start, target)
    )


def _observer_can_see(
    start: Position,
    target: Position,
    radius: int,
    obstacles: set[Position],
) -> bool:
    return (
        _distance(start, target) <= radius
        and _has_vision_line(start, target, obstacles)
    )


def _cell_visible_to_friendly(
    turn: Turn,
    target: Position,
    obstacles: set[Position],
) -> bool:
    if turn.core is not None and _observer_can_see(
        turn.core.position,
        target,
        CORE_VISION_RADIUS,
        obstacles,
    ):
        return True
    return any(
        _observer_can_see(
            unit.position,
            target,
            UNIT_VISION_RADII[unit.unit_type],
            obstacles,
        )
        for unit in turn.units
    )


def _ranger_line_range(start: Position, target: Position) -> int | None:
    dx = abs(target[0] - start[0])
    dy = abs(target[1] - start[1])
    if dx == 0 and dy == 0:
        return None
    if dx == 0 or dy == 0 or dx == dy:
        return max(dx, dy)
    return None


def _ranger_can_shoot(
    start: Position,
    target: Position,
    obstacles: set[Position],
) -> bool:
    line_range = _ranger_line_range(start, target)
    return (
        line_range is not None
        and 1 <= line_range <= 3
        and not any(
            cell in obstacles for cell in _intermediate_cells(start, target)
        )
    )


def _predicted_motion_cell(motion: EnemyUnitMotion | None) -> Position | None:
    if (
        motion is None
        or motion.movement_delta is None
        or motion.movement_observations < PREDICTION_MIN_OBSERVATIONS
    ):
        return None
    predicted = (
        motion.position[0] + motion.movement_delta[0],
        motion.position[1] + motion.movement_delta[1],
    )
    return predicted if _is_signed_int64_position(predicted) else None


def _enemy_threat_cells(
    enemies: Sequence[object],
    obstacles: set[Position],
) -> set[Position]:
    danger_cells: set[Position] = set()
    for enemy in enemies:
        unit_type = getattr(enemy, "unit_type", None)
        if unit_type is UnitType.VANGUARD:
            danger_cells.update(
                _destination(enemy.position, direction)
                for direction in CARDINAL_DIRECTIONS
            )
        elif unit_type is UnitType.RANGER:
            for dx, dy in RANGER_LINE_VECTORS:
                for distance in range(1, 4):
                    cell = (
                        enemy.position[0] + dx * distance,
                        enemy.position[1] + dy * distance,
                    )
                    if cell in obstacles:
                        break
                    danger_cells.add(cell)
    return danger_cells


def _projected_core_damage(
    core_position: Position,
    enemies: Sequence[object],
    obstacles: set[Position],
) -> int:
    damage = 0
    for enemy in enemies:
        if getattr(enemy, "kind", None) == "CORE":
            continue
        if enemy.unit_type is UnitType.VANGUARD:
            if _distance(core_position, enemy.position) == 1:
                damage += 1
        elif enemy.unit_type is UnitType.RANGER and _ranger_can_shoot(
            enemy.position,
            core_position,
            obstacles,
        ):
            damage += 1
    return damage


def _core_threatening_enemies(
    core_position: Position,
    enemies: Sequence[object],
    obstacles: set[Position],
) -> tuple[object, ...]:
    threats = []
    for enemy in enemies:
        if getattr(enemy, "kind", None) == "CORE":
            continue
        if enemy.unit_type is UnitType.VANGUARD:
            if _distance(core_position, enemy.position) == 1:
                threats.append(enemy)
        elif enemy.unit_type is UnitType.RANGER and _ranger_can_shoot(
            enemy.position,
            core_position,
            obstacles,
        ):
            threats.append(enemy)
    return tuple(threats)


def _guard_post(
    unit: Movable,
    core_position: Position,
    context: MovementContext,
    preferred_directions: Sequence[Direction],
    radius: int,
) -> Position:
    """Pick a stable outer post while keeping Core neighbors clear for cargo."""
    for direction in preferred_directions:
        dx, dy = direction.delta
        destination = (
            core_position[0] + dx * radius,
            core_position[1] + dy * radius,
        )
        if destination in context.obstacles:
            continue
        if destination in context.resource_cells:
            continue
        if destination in context.enemy_cells or destination in context.danger_cells:
            continue
        if destination in context.reserved_destinations:
            continue
        occupants = context.friendly_counts[destination]
        if destination == unit.position:
            return destination
        if occupants:
            continue
        return destination
    return unit.position


def _combat_target_key(origin: Position, enemy: object) -> tuple[object, ...]:
    unit_type = getattr(enemy, "unit_type", None)
    type_priority = (
        0
        if unit_type is UnitType.RANGER
        else 1
        if unit_type is UnitType.VANGUARD
        else 2
        if unit_type is UnitType.WORKER
        else 3
    )
    return (
        type_priority,
        getattr(enemy, "hp", 5),
        _distance(origin, enemy.position),
        _uuid_sort_key(enemy),
    )


def _projected_combat_target_key(
    origin: Position,
    enemy: object,
    planned_damage: Mapping[UUID, int],
) -> tuple[object, ...]:
    enemy_id = getattr(enemy, "id")
    remaining_hp = max(
        0,
        getattr(enemy, "hp", 5) - planned_damage.get(enemy_id, 0),
    )
    return (
        int(remaining_hp == 0),
        _combat_target_key(origin, enemy),
    )


def _record_planned_target_damage(
    target: object,
    planned_damage: dict[UUID, int],
) -> None:
    target_id = getattr(target, "id")
    planned_damage[target_id] = planned_damage.get(target_id, 0) + 1


def _record_planned_cell_damage(
    target_position: Position,
    enemies: Sequence[object],
    planned_damage: dict[UUID, int],
) -> None:
    for enemy in enemies:
        if enemy.position == target_position:
            _record_planned_target_damage(enemy, planned_damage)


def _queue_ranger_attack(
    ranger: object,
    target: object,
    visible_enemies: Sequence[object],
) -> None:
    occupants = sum(
        enemy.position == target.position for enemy in visible_enemies
    )
    if occupants > 1:
        ranger.shoot(target)
    else:
        ranger.shoot_cell(target.position)


def _defense_post_directions(
    core_position: Position,
    enemies: Sequence[object],
    fallback: Sequence[Direction],
    *,
    defender_index: int = 0,
    priority_ids: set[UUID] | None = None,
) -> tuple[Direction, ...]:
    combat_enemies = tuple(
        enemy
        for enemy in enemies
        if getattr(enemy, "kind", None) != "CORE"
        and getattr(enemy, "unit_type", None)
        in {UnitType.VANGUARD, UnitType.RANGER}
    )
    if not combat_enemies:
        return tuple(fallback)
    priority_ids = priority_ids or set()
    axis_enemies: dict[Direction, object] = {}
    for enemy in combat_enemies:
        axis = _directions_toward(core_position, enemy.position)[0]
        current = axis_enemies.get(axis)
        if current is None or (
            int(enemy.id not in priority_ids),
            _distance(core_position, enemy.position),
            _combat_target_key(core_position, enemy),
        ) < (
            int(current.id not in priority_ids),
            _distance(core_position, current.position),
            _combat_target_key(core_position, current),
        ):
            axis_enemies[axis] = enemy
    ordered_axes = tuple(
        axis
        for axis, _ in sorted(
            axis_enemies.items(),
            key=lambda item: (
                int(item[1].id not in priority_ids),
                _distance(core_position, item[1].position),
                _combat_target_key(core_position, item[1]),
                CARDINAL_DIRECTIONS.index(item[0]),
            ),
        )
    )
    primary = ordered_axes[defender_index % len(ordered_axes)]
    return (primary,) + tuple(
        direction
        for direction in _directions_toward(
            core_position,
            axis_enemies[primary].position,
        )
        if direction is not primary
    )


def _worker_expansion_threshold(
    worker_count: int,
    worker_target: int,
    resource_capacity: int,
    population: int,
) -> int:
    next_worker_cost = unit_cost(UnitType.WORKER, population)
    if worker_count < BASE_WORKER_TARGET:
        return min(
            CORE_RESOURCE_RESERVE + next_worker_cost,
            resource_capacity,
        )

    completed_late_stages = (worker_count - BASE_WORKER_TARGET) // 2
    stage_target = min(
        worker_target,
        BASE_WORKER_TARGET + 2 * (completed_late_stages + 1),
    )
    remaining_stage_workers = max(1, stage_target - worker_count)
    stage_cost = sum(
        unit_cost(UnitType.WORKER, population + offset)
        for offset in range(remaining_stage_workers)
    )
    return LATE_EXPANSION_RESERVE + stage_cost


def _uuid_sort_key(obj: object) -> bytes:
    identifier = getattr(obj, "id")
    return getattr(identifier, "bytes")


def _unit_max_hp(unit_type: UnitType) -> int:
    return 4 if unit_type is UnitType.VANGUARD else 2


def _projected_core_resources(turn: Turn) -> int:
    plan = turn.plan.model_dump(mode="json", exclude_none=True)
    unit_actions = plan.get("unit_actions", {})
    depositing_ids = {
        unit_id
        for unit_id, action in unit_actions.items()
        if action.get("type") == "DEPOSIT"
    }
    deposited = min(
        turn.resource_space,
        sum(
            worker.cargo
            for worker in turn.workers
            if str(worker.id) in depositing_ids
        ),
    )
    projected = turn.resources + deposited
    healing_reserve = sum(
        _unit_max_hp(unit.unit_type) - 1
        for unit in turn.units
        if unit_actions.get(str(unit.id), {}).get("type") == "HEAL"
    )
    return max(0, projected - healing_reserve)


class CoreFarmer:
    def __init__(
        self,
        *,
        worker_target: int = DEFAULT_WORKER_TARGET,
        beacon_policy: str = DEFAULT_BEACON_POLICY,
        compatibility_marker: Path | None = DEFAULT_COMPATIBILITY_MARKER,
    ) -> None:
        if not 1 <= worker_target <= MAX_WORKER_TARGET:
            raise ValueError(
                f"worker_target must be between 1 and {MAX_WORKER_TARGET}"
            )
        if beacon_policy not in {"hold", "pursue", "retreat"}:
            raise ValueError("beacon_policy must be 'hold', 'pursue', or 'retreat'")
        self.worker_target = worker_target
        self.beacon_policy = beacon_policy
        self.compatibility_marker = compatibility_marker
        self.compatibility_hold = False
        self.known_obstacles: set[Position] = set()
        self.scout_slots: dict[UUID, int] = {}
        self.scout_stages: dict[UUID, int] = {}
        self.scout_progress: dict[UUID, ScoutProgress] = {}
        self.scout_target_last_visited: dict[Position, int] = {}
        self.scout_claims: set[Position] = set()
        self.scout_active_chunks: dict[UUID, Position] = {}
        self.scout_chunk_last_seen: dict[Position, int] = {}
        self.worker_history: dict[UUID, deque[Position]] = {}
        self.resource_last_seen: dict[Position, int] = {}
        self.resource_intents: dict[UUID, Position] = {}
        self.resource_progress: dict[UUID, ResourceProgress] = {}
        self.resource_cooldowns: dict[tuple[UUID, Position], int] = {}
        self.worker_modes: dict[UUID, str] = {}
        self.worker_targets: dict[UUID, Position] = {}
        self.last_danger_cells: set[Position] = set()
        self.last_released_targets: dict[UUID, Position] = {}
        self.recovery_until_tick = 0
        self.recovery_reason = "NONE"
        self.last_core_move_tick = -RETREAT_SERVICE_TICKS
        self.last_retreat_direction: Direction | None = None
        self.active_core_move_reason: str | None = None
        self.last_core_cancel_reason = "NONE"
        self.last_projected_core_damage = 0
        self.last_core_survival_margin = 0
        self.enemy_core_sightings: dict[UUID, EnemyCoreSighting] = {}
        self.enemy_unit_sightings: dict[UUID, EnemyCoreSighting] = {}
        self.enemy_unit_motion: dict[UUID, EnemyUnitMotion] = {}
        self.active_enemy_ids: set[UUID] = set()
        self.preemptive_evade_enemy_ids: set[UUID] = set()
        self.pursuing_enemy_ids: set[UUID] = set()
        self.recent_attack_until_tick = 0
        self.recent_core_attack_until_tick = 0
        self.recent_attack_threats: dict[UUID, RememberedThreat] = {}
        self.threat_assessment = ThreatAssessment()
        self.combat_pressure_active = False
        self.squad_return_ids: set[UUID] = set()
        self.scout_return_ids: set[UUID] = set()
        self.scout_cooldown_until: dict[UUID, int] = {}
        self.squad_disengage_until_tick = 0
        self.healing_defender_ids: set[UUID] = set()
        self.stationary_core_memory: dict[UUID, EnemyCoreSighting] = {}
        self.isolated_core_target_id: UUID | None = None
        self.raid_mode: RaidMode | None = None
        self.raid_phase: RaidPhase | None = None
        self.raid_vanguard_ids: set[UUID] = set()
        self.raid_ranger_ids: set[UUID] = set()
        self.raid_stage_assignments: dict[UUID, Position] = {}
        self.raid_initial_member_hp: dict[UUID, int] = {}
        self.raid_initial_defender_ids: set[UUID] = set()
        self.raid_target_position: Position | None = None
        self.raid_target_last_durability: int | None = None
        self.raid_last_objective_distance: int | None = None
        self.raid_last_defender_hp: int | None = None
        self.raid_last_progress_tick = 0
        self.raid_started_tick = 0
        self.raid_abort_reason = "NONE"
        self.raid_reserved_resources = 0
        self.raid_rebuild_vanguard_target = 0
        self.raid_rebuild_ranger_target = 0
        self.active_raid_episode: RaidEpisode | None = None
        self.raid_episode_history: deque[RaidEpisode] = deque(
            maxlen=RAID_EPISODE_HISTORY_LIMIT,
        )
        self.raid_target_cooldown_until: dict[UUID, int] = {}
        self.core_observer_candidates: dict[UUID, UUID] = {}
        self.core_observer_target_id: UUID | None = None
        self.core_raid_spotter_id: UUID | None = None
        self.stationary_unit_target_id: UUID | None = None
        self.threat_caution_until_tick = 0
        self.startup_tick: int | None = None

    @property
    def recovery_mode(self) -> bool:
        return self.recovery_until_tick > 0

    def strategy_phase(self, turn: Turn) -> str:
        if turn.core is None:
            return "RESPAWNING"
        if self.compatibility_hold:
            return "COMPATIBILITY_HOLD"
        if self.recovery_mode:
            return "RECOVERY"
        if (
            self.isolated_core_target_id is not None
            or self.stationary_unit_target_id is not None
        ):
            if (
                self.isolated_core_target_id is not None
                and self.raid_phase is not None
            ):
                return f"RAID_{self.raid_phase.value}"
            return "CLEAR_CORE"
        early_worker_goal = min(EARLY_DEFENSE_WORKER_GOAL, self.worker_target)
        if len(turn.workers) < early_worker_goal:
            return "EXPANSION"
        if (
            len(turn.vanguards) < EARLY_DEFENSE_VANGUARD_TARGET
            or len(turn.rangers) < EARLY_DEFENSE_RANGER_TARGET
        ):
            return "FORTIFY"
        if len(turn.workers) < min(MIDGAME_WORKER_GOAL, self.worker_target):
            return "EXPANSION"
        if (
            len(turn.vanguards) < min(MIDGAME_VANGUARD_TARGET, DEFENSE_VANGUARD_TARGET)
            or len(turn.rangers) < min(MIDGAME_RANGER_TARGET, DEFENSE_RANGER_TARGET)
        ):
            return "FORTIFY"
        if len(turn.workers) < self.worker_target:
            return "EXPANSION"
        if (
            len(turn.vanguards) < DEFENSE_VANGUARD_TARGET
            or len(turn.rangers) < DEFENSE_RANGER_TARGET
        ):
            return "FORTIFY"
        return "STOCKPILE"

    def _refresh_compatibility_hold(self) -> None:
        if self.compatibility_marker is None:
            self.compatibility_hold = False
            return
        try:
            self.compatibility_hold = self.compatibility_marker.exists()
        except OSError:
            self.compatibility_hold = True

    def _release_core_observer(self) -> None:
        self.core_observer_target_id = None
        self.core_raid_spotter_id = None

    def _start_raid_episode(
        self,
        turn: Turn,
        target: object,
        raid_members: Sequence[object],
        defenders: Sequence[object],
    ) -> None:
        # A new tactical raid may start as soon as the strategy is ready again,
        # even if an older episode was still waiting for a delayed observer
        # return.  Keep the telemetry lossless by closing that older record
        # explicitly before replacing the active pointer.
        if self.active_raid_episode is not None:
            self._interrupt_raid_episode(turn, "SUPERSEDED")
        self.active_raid_episode = RaidEpisode(
            target_id=target.id,
            mode=self.raid_mode or RaidMode.CUT,
            start_tick=turn.tick,
            start_resources=turn.resources,
            start_vanguard_count=len(turn.vanguards),
            start_ranger_count=len(turn.rangers),
            initial_member_ids=frozenset(unit.id for unit in raid_members),
            initial_member_hp=sum(unit.hp for unit in raid_members),
            initial_defender_count=len(defenders),
            initial_target_durability=self.raid_target_last_durability,
            rebuild_vanguard_target=self.raid_rebuild_vanguard_target,
            rebuild_ranger_target=self.raid_rebuild_ranger_target,
            last_target_durability=self.raid_target_last_durability,
            surviving_member_ids=frozenset(unit.id for unit in raid_members),
        )

    def _mark_raid_episode_ready(
        self,
        turn: Turn,
        *,
        cycle_end_reason: str = "READY",
        force: bool = False,
    ) -> None:
        episode = self.active_raid_episode
        if episode is None:
            return
        if episode.engagement_end_tick is None:
            if not force:
                return
            episode.engagement_end_tick = turn.tick
            episode.engagement_end_resources = turn.resources
            episode.outcome = cycle_end_reason
        living_ids = {
            unit.id
            for unit in (*turn.vanguards, *turn.rangers)
            if unit.id in episode.initial_member_ids
        }
        episode.surviving_member_ids = frozenset(living_ids)
        if episode.squad_return_complete_tick is None:
            episode.squad_return_complete_tick = turn.tick
        if episode.scout_return_complete_tick is None:
            episode.scout_return_complete_tick = turn.tick
        if episode.rebuild_complete_tick is None:
            episode.rebuild_complete_tick = turn.tick
        episode.ready_tick = turn.tick
        episode.ready_resources = turn.resources
        episode.ready_vanguard_count = len(turn.vanguards)
        episode.ready_ranger_count = len(turn.rangers)
        episode.cycle_end_reason = cycle_end_reason
        self.raid_episode_history.append(episode)
        self.active_raid_episode = None

    def _end_raid_episode(
        self,
        turn: Turn,
        outcome: str,
        *,
        force_ready: bool = False,
        cycle_end_reason: str = "PENDING",
    ) -> None:
        episode = self.active_raid_episode
        if episode is None or episode.engagement_end_tick is not None:
            return
        episode.outcome = outcome
        episode.engagement_end_tick = turn.tick
        episode.engagement_end_resources = turn.resources
        episode.last_target_durability = self.raid_target_last_durability
        episode.surviving_member_ids = frozenset(
            unit.id
            for unit in (*turn.vanguards, *turn.rangers)
            if unit.id in episode.initial_member_ids
        )
        episode.return_member_ids = frozenset(
            episode.surviving_member_ids & self.squad_return_ids
        )
        if episode.spotter_id is not None and episode.spotter_id in self.scout_return_ids:
            episode.return_spotter_ids = frozenset({episode.spotter_id})
        if not episode.return_member_ids:
            episode.squad_return_complete_tick = turn.tick
        if not episode.return_spotter_ids:
            episode.scout_return_complete_tick = turn.tick
        if (
            len(turn.vanguards) >= episode.rebuild_vanguard_target
            and len(turn.rangers) >= episode.rebuild_ranger_target
        ):
            episode.rebuild_complete_tick = turn.tick
        if force_ready:
            self._mark_raid_episode_ready(
                turn,
                cycle_end_reason=cycle_end_reason or outcome,
                force=True,
            )

    def _interrupt_raid_episode(self, turn: Turn, reason: str) -> None:
        episode = self.active_raid_episode
        if episode is None:
            return
        if episode.engagement_end_tick is None:
            self._end_raid_episode(
                turn,
                reason,
                force_ready=True,
                cycle_end_reason=reason,
            )
        else:
            self._mark_raid_episode_ready(
                turn,
                cycle_end_reason=reason,
                force=True,
            )

    def _refresh_raid_episode(self, turn: Turn) -> None:
        episode = self.active_raid_episode
        if episode is None or episode.engagement_end_tick is None:
            return
        living_ids = {
            unit.id
            for unit in (*turn.vanguards, *turn.rangers)
            if unit.id in episode.initial_member_ids
        }
        episode.surviving_member_ids = frozenset(living_ids)
        if episode.return_member_ids.isdisjoint(self.squad_return_ids):
            episode.squad_return_complete_tick = (
                episode.squad_return_complete_tick or turn.tick
            )
        if episode.return_spotter_ids.isdisjoint(self.scout_return_ids):
            episode.scout_return_complete_tick = (
                episode.scout_return_complete_tick or turn.tick
            )
        if (
            len(turn.vanguards) >= episode.rebuild_vanguard_target
            and len(turn.rangers) >= episode.rebuild_ranger_target
        ):
            episode.rebuild_complete_tick = (
                episode.rebuild_complete_tick or turn.tick
            )
        else:
            # A unit can be lost after the engagement has ended while the
            # strike group is travelling home.  Do not retain the provisional
            # completion mark from the engagement tick; the episode must wait
            # for the replacement fleet before it is archived.
            episode.rebuild_complete_tick = None
        if (
            episode.squad_return_complete_tick is not None
            and episode.scout_return_complete_tick is not None
            and episode.rebuild_complete_tick is not None
        ):
            self._mark_raid_episode_ready(turn)

    def _release_core_raid(self, *, forget_position: bool = False) -> None:
        target_id = self.isolated_core_target_id
        self.isolated_core_target_id = None
        self.raid_mode = None
        self.raid_phase = None
        self.raid_vanguard_ids.clear()
        self.raid_ranger_ids.clear()
        self.raid_stage_assignments.clear()
        self.raid_initial_member_hp.clear()
        self.raid_initial_defender_ids.clear()
        self.raid_target_position = None
        self.raid_target_last_durability = None
        self.raid_last_objective_distance = None
        self.raid_last_defender_hp = None
        self.raid_last_progress_tick = 0
        self.raid_started_tick = 0
        self.raid_reserved_resources = 0
        if target_id is not None and forget_position:
            self.stationary_core_memory.pop(target_id, None)
            self.core_observer_candidates.pop(target_id, None)
        if self.core_observer_target_id == target_id:
            self._release_core_observer()

    def _infer_core_observer(self, turn: Turn, enemy_core: object) -> UUID | None:
        obstacles = set(self.known_obstacles) | set(turn.obstacle_cells)
        candidates = [
            worker
            for worker in turn.workers
            if worker.cargo == 0
            and worker.position not in turn.resource_cells
            and _observer_can_see(
                worker.position,
                enemy_core.position,
                CORE_OBSERVER_MAX_DISTANCE,
                obstacles,
            )
        ]
        if not candidates:
            return None
        newly_exposing = [
            worker
            for worker in candidates
            if not self.worker_history.get(worker.id)
            or not _observer_can_see(
                self.worker_history[worker.id][-1],
                enemy_core.position,
                CORE_OBSERVER_MAX_DISTANCE,
                obstacles,
            )
        ]
        pool = newly_exposing or candidates
        return min(
            pool,
            key=lambda worker: (
                abs(
                    _distance(worker.position, enemy_core.position)
                    - CORE_OBSERVER_MAX_DISTANCE
                ),
                _uuid_sort_key(worker),
            ),
        ).id

    @staticmethod
    def _core_is_protected(turn: Turn, position: Position) -> bool:
        return bool(CoreFarmer._core_defenders(turn, position))

    @staticmethod
    def _core_defenders(
        turn: Turn,
        position: Position,
        *,
        radius: int = CORE_RAID_REINFORCEMENT_RADIUS,
    ) -> tuple[object, ...]:
        return tuple(
            enemy
            for enemy in turn.visible_enemies
            if getattr(enemy, "kind", None) != "CORE"
            and getattr(enemy, "unit_type", None)
            in {UnitType.VANGUARD, UnitType.RANGER}
            and _distance(enemy.position, position) <= radius
        )

    def _raid_local_opponents(self, turn: Turn) -> tuple[object, ...]:
        members = self._raid_members(turn)
        return tuple(
            enemy
            for enemy in turn.visible_enemies
            if getattr(enemy, "kind", None) != "CORE"
            and getattr(enemy, "unit_type", None)
            in {UnitType.VANGUARD, UnitType.RANGER}
            and any(
                _distance(member.position, enemy.position)
                <= UNIT_EVADE_TRIGGER_DISTANCE
                for member in members
            )
        )

    def _raid_breach_opponents(
        self,
        turn: Turn,
        target_position: Position,
    ) -> tuple[object, ...]:
        opponents = {
            enemy.id: enemy
            for enemy in self._core_defenders(turn, target_position)
        }
        opponents.update(
            {enemy.id: enemy for enemy in self._raid_local_opponents(turn)}
        )
        return tuple(opponents.values())

    @staticmethod
    def _combat_power(
        units: Sequence[object],
        target: Position,
        obstacles: set[Position],
    ) -> int:
        power = 0
        for unit in units:
            hp = max(0, getattr(unit, "hp", 0))
            if unit.unit_type is UnitType.VANGUARD:
                power += hp + 1 + int(_distance(unit.position, target) <= 2)
            elif unit.unit_type is UnitType.RANGER:
                power += hp + 2 + int(
                    _ranger_can_shoot(unit.position, target, obstacles)
                )
        return power

    def _raid_members(self, turn: Turn) -> tuple[object, ...]:
        raid_ids = self.raid_vanguard_ids | self.raid_ranger_ids
        return tuple(unit for unit in turn.units if unit.id in raid_ids)

    def _home_guard_counts(
        self,
        turn: Turn,
        target_position: Position,
    ) -> tuple[int, int]:
        core = turn.core
        if core is None:
            return VANGUARD_CORE_GUARDS, RANGER_CORE_GUARDS
        home_threats = tuple(
            enemy
            for enemy in turn.visible_enemies
            if getattr(enemy, "kind", None) != "CORE"
            and getattr(enemy, "unit_type", None)
            in {UnitType.VANGUARD, UnitType.RANGER}
            and _distance(enemy.position, core.position)
            <= CORE_RAID_HOME_RESPONSE_RADIUS
            and _distance(enemy.position, core.position) + 2
            < _distance(enemy.position, target_position)
        )
        extra_guard = int(bool(home_threats))
        return (
            min(
                max(0, len(turn.vanguards) - 1),
                VANGUARD_CORE_GUARDS + extra_guard,
            ),
            min(
                max(0, len(turn.rangers) - 1),
                RANGER_CORE_GUARDS + extra_guard,
            ),
        )

    def _prospective_raid_groups(
        self,
        turn: Turn,
        target_position: Position,
    ) -> tuple[tuple[object, ...], tuple[object, ...]]:
        vanguard_guards, ranger_guards = self._home_guard_counts(
            turn,
            target_position,
        )
        available_vanguards = sorted(
            (
                unit
                for unit in turn.vanguards
                if unit.id not in self.squad_return_ids
            ),
            key=lambda unit: (
                _distance(unit.position, turn.core.position),
                _uuid_sort_key(unit),
            ),
        )
        available_rangers = sorted(
            (
                unit
                for unit in turn.rangers
                if unit.id not in self.squad_return_ids
            ),
            key=lambda unit: (
                _distance(unit.position, turn.core.position),
                _uuid_sort_key(unit),
            ),
        )
        return (
            tuple(available_vanguards[vanguard_guards:]),
            tuple(available_rangers[ranger_guards:]),
        )

    def _raid_rebuild_missing(self, turn: Turn) -> tuple[int, int]:
        return (
            max(0, self.raid_rebuild_vanguard_target - len(turn.vanguards)),
            max(0, self.raid_rebuild_ranger_target - len(turn.rangers)),
        )

    def _clear_completed_raid_rebuild(self, turn: Turn) -> None:
        if self.isolated_core_target_id is not None:
            return
        missing_vanguards, missing_rangers = self._raid_rebuild_missing(turn)
        if missing_vanguards == 0 and missing_rangers == 0:
            self.raid_rebuild_vanguard_target = 0
            self.raid_rebuild_ranger_target = 0

    def _select_raid_groups(
        self,
        turn: Turn,
        target_position: Position,
    ) -> tuple[tuple[object, ...], tuple[object, ...]] | None:
        available_vanguards, available_rangers = self._prospective_raid_groups(
            turn,
            target_position,
        )
        if not available_vanguards or not available_rangers:
            return None

        defenders = self._core_defenders(turn, target_position)
        if not defenders:
            vanguards = tuple(
                sorted(
                    available_vanguards,
                    key=lambda unit: (
                        _distance(unit.position, target_position),
                        _uuid_sort_key(unit),
                    ),
                )[:CORE_RAID_CUT_VANGUARDS]
            )
            rangers = tuple(
                sorted(
                    available_rangers,
                    key=lambda unit: (
                        _distance(unit.position, target_position),
                        _uuid_sort_key(unit),
                    ),
                )[:CORE_RAID_CUT_RANGERS]
            )
            return vanguards, rangers

        required_power = self._combat_power(
            defenders,
            target_position,
            self.known_obstacles,
        ) + CORE_RAID_SUPERIORITY_MARGIN
        all_available = (*available_vanguards, *available_rangers)
        if (
            self._combat_power(
                all_available,
                target_position,
                self.known_obstacles,
            )
            < required_power
        ):
            return None

        # Combat power is additive, so the strongest prefix for a given
        # V/R split is sufficient to prove whether any formation of that split
        # can win. Searching only those prefixes preserves the smallest-squad
        # rule while keeping the work quadratic instead of exponential as the
        # fleet grows.
        strongest_vanguards = tuple(
            sorted(
                available_vanguards,
                key=lambda unit: (
                    -self._combat_power(
                        (unit,),
                        target_position,
                        self.known_obstacles,
                    ),
                    _distance(unit.position, target_position),
                    _uuid_sort_key(unit),
                ),
            )
        )
        strongest_rangers = tuple(
            sorted(
                available_rangers,
                key=lambda unit: (
                    -self._combat_power(
                        (unit,),
                        target_position,
                        self.known_obstacles,
                    ),
                    _distance(unit.position, target_position),
                    _uuid_sort_key(unit),
                ),
            )
        )
        for member_count in range(2, len(all_available) + 1):
            best: tuple[
                tuple[object, ...],
                tuple[object, ...],
            ] | None = None
            best_key: tuple[object, ...] | None = None
            min_vanguards = max(1, member_count - len(available_rangers))
            max_vanguards = min(
                len(available_vanguards),
                member_count - 1,
            )
            for vanguard_count in range(min_vanguards, max_vanguards + 1):
                ranger_count = member_count - vanguard_count
                if ranger_count > len(strongest_rangers):
                    continue
                vanguards = strongest_vanguards[:vanguard_count]
                rangers = strongest_rangers[:ranger_count]
                members = (*vanguards, *rangers)
                if self._combat_power(
                    members,
                    target_position,
                    self.known_obstacles,
                ) < required_power:
                    continue
                distances = tuple(
                    _distance(unit.position, target_position)
                    for unit in members
                )
                key = (
                    abs(len(vanguards) - len(rangers)),
                    sum(distances),
                    max(distances),
                    tuple(sorted(_uuid_sort_key(unit) for unit in members)),
                )
                if best_key is None or key < best_key:
                    best_key = key
                    best = vanguards, rangers
            if best is not None:
                return best
        return None

    def _raid_loss_budget(
        self,
        turn: Turn,
        target_position: Position,
        vanguards: Sequence[object],
        rangers: Sequence[object],
        defenders: Sequence[object],
    ) -> int:
        if not defenders:
            return 0
        members = (*vanguards, *rangers)
        friendly_power = self._combat_power(
            members,
            target_position,
            self.known_obstacles,
        )
        enemy_power = self._combat_power(
            defenders,
            target_position,
            self.known_obstacles,
        )
        population = len(turn.units)
        deployed_replacement_value = sum(
            unit_cost(unit.unit_type, population) for unit in members
        )
        expected_loss = math.ceil(
            deployed_replacement_value
            * enemy_power
            / friendly_power
            * CORE_RAID_MAX_HP_LOSS_RATIO
        )
        return max(ISOLATED_CORE_MIN_RESOURCES, expected_loss)

    def _raid_has_superiority(
        self,
        turn: Turn,
        target_position: Position,
        vanguards: Sequence[object],
        rangers: Sequence[object],
    ) -> bool:
        if not vanguards or not rangers:
            return False
        friendly_power = self._combat_power(
            (*vanguards, *rangers),
            target_position,
            self.known_obstacles,
        )
        enemy_power = self._combat_power(
            self._core_defenders(turn, target_position),
            target_position,
            self.known_obstacles,
        )
        return friendly_power >= enemy_power + CORE_RAID_SUPERIORITY_MARGIN

    @staticmethod
    def _raid_stage_points(
        core_position: Position,
        target_position: Position,
    ) -> tuple[Position, Position]:
        dx = target_position[0] - core_position[0]
        dy = target_position[1] - core_position[1]
        if abs(dx) >= abs(dy):
            approach = (1 if dx >= 0 else -1, 0)
            flank = (0, 1)
        else:
            approach = (0, 1 if dy >= 0 else -1)
            flank = (1, 0)
        rear = (
            target_position[0] - approach[0] * CORE_RAID_STAGE_DISTANCE,
            target_position[1] - approach[1] * CORE_RAID_STAGE_DISTANCE,
        )
        flank_offset = max(2, CORE_RAID_STAGE_DISTANCE // 2)
        return (
            (
                rear[0] + flank[0] * flank_offset,
                rear[1] + flank[1] * flank_offset,
            ),
            (
                rear[0] - flank[0] * flank_offset,
                rear[1] - flank[1] * flank_offset,
            ),
        )

    def _raid_members_attack_ready(
        self,
        turn: Turn,
        target_position: Position,
    ) -> bool:
        units_by_id = {unit.id: unit for unit in turn.units}
        return bool(self.raid_vanguard_ids and self.raid_ranger_ids) and all(
            unit_id in units_by_id
            and _distance(units_by_id[unit_id].position, target_position) == 1
            for unit_id in self.raid_vanguard_ids
        ) and all(
            unit_id in units_by_id
            and _ranger_can_shoot(
                units_by_id[unit_id].position,
                target_position,
                self.known_obstacles,
            )
            for unit_id in self.raid_ranger_ids
        )

    def _raid_stage_complete(self, turn: Turn) -> bool:
        units_by_id = {unit.id: unit for unit in turn.units}
        return bool(self.raid_stage_assignments) and all(
            unit_id in units_by_id
            and _distance(units_by_id[unit_id].position, position)
            <= CORE_RAID_STAGE_TOLERANCE
            for unit_id, position in self.raid_stage_assignments.items()
        )

    def _raid_stage_distance(self, turn: Turn) -> int:
        units_by_id = {unit.id: unit for unit in turn.units}
        return sum(
            _distance(units_by_id[unit_id].position, position)
            for unit_id, position in self.raid_stage_assignments.items()
            if unit_id in units_by_id
        )

    def _raid_breach_distance(
        self,
        turn: Turn,
        target_position: Position,
        opponents: Sequence[object],
    ) -> int:
        destinations = tuple(enemy.position for enemy in opponents) or (
            target_position,
        )
        distance = 0
        for member in self._raid_members(turn):
            nearest = min(_distance(member.position, point) for point in destinations)
            if member.unit_type is UnitType.VANGUARD:
                distance += max(0, nearest - 1)
            elif any(
                _ranger_can_shoot(
                    member.position,
                    point,
                    self.known_obstacles,
                )
                for point in destinations
            ):
                continue
            else:
                distance += max(1, nearest - 3)
        return distance

    def _initialize_core_raid(
        self,
        turn: Turn,
        target: object,
    ) -> bool:
        defenders = self._core_defenders(turn, target.position)
        selected_groups = self._select_raid_groups(
            turn,
            target.position,
        )
        if selected_groups is None:
            return False
        vanguards, rangers = selected_groups
        loss_budget = self._raid_loss_budget(
            turn,
            target.position,
            vanguards,
            rangers,
            defenders,
        )
        if defenders and turn.resources < loss_budget:
            return False

        self.isolated_core_target_id = target.id
        self.raid_mode = RaidMode.SIEGE if defenders else RaidMode.CUT
        self.raid_vanguard_ids = {unit.id for unit in vanguards}
        self.raid_ranger_ids = {unit.id for unit in rangers}
        raid_members = (*vanguards, *rangers)
        self.raid_initial_member_hp = {
            unit.id: unit.hp for unit in raid_members
        }
        self.raid_initial_defender_ids = {enemy.id for enemy in defenders}
        self.raid_target_position = target.position
        self.raid_target_last_durability = target.hp + target.shield
        self.raid_started_tick = turn.tick
        self.raid_last_progress_tick = turn.tick
        self.raid_abort_reason = "NONE"
        self.raid_reserved_resources = loss_budget
        self.raid_rebuild_vanguard_target = max(
            self.raid_rebuild_vanguard_target,
            len(turn.vanguards),
        )
        self.raid_rebuild_ranger_target = max(
            self.raid_rebuild_ranger_target,
            len(turn.rangers),
        )
        self._start_raid_episode(
            turn,
            target,
            raid_members,
            defenders,
        )

        self.raid_last_defender_hp = sum(enemy.hp for enemy in defenders)
        if self.raid_mode is RaidMode.CUT:
            self.raid_stage_assignments.clear()
            self.raid_phase = RaidPhase.CORE_FOCUS
            self.raid_last_objective_distance = _core_raid_strike_distance(
                target.position,
                vanguards,
                rangers,
            )
        else:
            stage_points = self._raid_stage_points(
                turn.core.position,
                target.position,
            )
            self.raid_stage_assignments = {
                unit.id: stage_points[index % len(stage_points)]
                for index, unit in enumerate(
                    sorted(raid_members, key=_uuid_sort_key)
                )
            }
            self.raid_last_objective_distance = self._raid_stage_distance(turn)
            if self._raid_members_attack_ready(turn, target.position):
                self.raid_phase = RaidPhase.BREACH
                self.raid_last_objective_distance = None
            else:
                self.raid_phase = RaidPhase.STAGE
        return True

    def _complete_core_raid(self, turn: Turn) -> None:
        raid_ids = self.raid_vanguard_ids | self.raid_ranger_ids
        living_defender_ids = {
            unit.id for unit in (*turn.vanguards, *turn.rangers)
        }
        self.squad_return_ids.update(raid_ids & living_defender_ids)
        if self.core_raid_spotter_id is not None:
            self.scout_return_ids.add(self.core_raid_spotter_id)
        self.squad_disengage_until_tick = max(
            self.squad_disengage_until_tick,
            turn.tick + SQUAD_DISENGAGE_TICKS,
        )
        self.raid_abort_reason = "COMPLETED"
        self._end_raid_episode(turn, "COMPLETED")
        self._release_core_raid(forget_position=True)

    def _abort_core_raid(
        self,
        turn: Turn,
        reason: str,
        *,
        forget_position: bool = False,
    ) -> None:
        target_id = self.isolated_core_target_id
        raid_ids = self.raid_vanguard_ids | self.raid_ranger_ids
        living_defender_ids = {
            unit.id for unit in (*turn.vanguards, *turn.rangers)
        }
        if raid_ids:
            self.squad_return_ids.update(raid_ids & living_defender_ids)
            if self.core_raid_spotter_id is not None:
                self.scout_return_ids.add(self.core_raid_spotter_id)
            self.squad_disengage_until_tick = max(
                self.squad_disengage_until_tick,
                turn.tick + SQUAD_DISENGAGE_TICKS,
            )
        else:
            target = self._active_raid_target_for_recall()
            if target is not None:
                self._recall_strike_group(turn, target)
        if target_id is not None:
            self.raid_target_cooldown_until[target_id] = (
                turn.tick + CORE_RAID_TARGET_COOLDOWN_TICKS
            )
        self.raid_abort_reason = reason
        self._end_raid_episode(turn, reason)
        self._release_core_raid(forget_position=forget_position)

    def _raid_abort_reason_for_turn(
        self,
        turn: Turn,
        target_position: Position,
        visible_target: object | None,
    ) -> str | None:
        raid_ids = self.raid_vanguard_ids | self.raid_ranger_ids
        members = self._raid_members(turn)
        living_ids = {unit.id for unit in members}
        if raid_ids - living_ids:
            return "MEMBER_LOST"

        initial_hp = sum(self.raid_initial_member_hp.values())
        current_hp = sum(unit.hp for unit in members)
        if initial_hp and current_hp < initial_hp * (1 - CORE_RAID_MAX_HP_LOSS_RATIO):
            return "HP_BUDGET_EXCEEDED"

        if visible_target is not None and visible_target.position != target_position:
            return "TARGET_MOVED"

        current_defenders = self._core_defenders(turn, target_position)
        new_defenders = {
            enemy.id for enemy in current_defenders
        } - self.raid_initial_defender_ids
        if new_defenders and not self._raid_has_superiority(
            turn,
            target_position,
            tuple(unit for unit in members if unit.unit_type is UnitType.VANGUARD),
            tuple(unit for unit in members if unit.unit_type is UnitType.RANGER),
        ):
            return "REINFORCED"

        return None

    def _advance_core_raid(
        self,
        turn: Turn,
        target_position: Position,
        visible_target: object | None,
    ) -> str | None:
        abort_reason = self._raid_abort_reason_for_turn(
            turn,
            target_position,
            visible_target,
        )
        if abort_reason is not None:
            return abort_reason

        if visible_target is not None:
            durability = visible_target.hp + visible_target.shield
            if (
                self.raid_target_last_durability is None
                or durability < self.raid_target_last_durability
            ):
                self.raid_last_progress_tick = turn.tick
            self.raid_target_last_durability = durability

        if self.raid_phase is RaidPhase.STAGE:
            stage_distance = self._raid_stage_distance(turn)
            if (
                self.raid_last_objective_distance is None
                or stage_distance < self.raid_last_objective_distance
            ):
                self.raid_last_progress_tick = turn.tick
            self.raid_last_objective_distance = stage_distance
            if self._raid_stage_complete(turn):
                self.raid_phase = RaidPhase.BREACH
                self.raid_last_objective_distance = None
                self.raid_last_defender_hp = None
                self.raid_last_progress_tick = turn.tick

        if self.raid_phase is RaidPhase.BREACH:
            opponents = self._raid_breach_opponents(
                turn,
                target_position,
            )
            defender_hp = sum(enemy.hp for enemy in opponents)
            breach_distance = self._raid_breach_distance(
                turn,
                target_position,
                opponents,
            )
            if (
                self.raid_last_defender_hp is None
                or defender_hp < self.raid_last_defender_hp
                or self.raid_last_objective_distance is None
                or breach_distance < self.raid_last_objective_distance
            ):
                self.raid_last_progress_tick = turn.tick
            self.raid_last_defender_hp = defender_hp
            self.raid_last_objective_distance = breach_distance
            if not opponents and self._raid_members_attack_ready(
                turn,
                target_position,
            ):
                self.raid_phase = RaidPhase.CORE_FOCUS
                self.raid_last_progress_tick = turn.tick
                self.raid_last_objective_distance = 0

        if self.raid_phase is RaidPhase.CORE_FOCUS:
            vanguards = tuple(
                unit
                for unit in turn.vanguards
                if unit.id in self.raid_vanguard_ids
            )
            rangers = tuple(
                unit
                for unit in turn.rangers
                if unit.id in self.raid_ranger_ids
            )
            if vanguards and rangers:
                strike_distance = _core_raid_strike_distance(
                    target_position,
                    vanguards,
                    rangers,
                )
                if (
                    self.raid_last_objective_distance is None
                    or strike_distance < self.raid_last_objective_distance
                ):
                    self.raid_last_progress_tick = turn.tick
                self.raid_last_objective_distance = strike_distance

        if (
            self.raid_phase is not None
            and turn.tick - self.raid_last_progress_tick
            >= CORE_RAID_NO_PROGRESS_TICKS
        ):
            return "NO_PROGRESS"
        return None

    def _home_defense_pressure(self) -> bool:
        assessment = self.threat_assessment
        return bool(
            assessment.recent_attack
            or assessment.recent_core_attack
            or assessment.preemptive_enemy_ids
            or assessment.pursuing_enemy_ids
            or assessment.near_core_enemy_ids
            or assessment.threatening_core_enemy_ids
            or assessment.disengaging
        )

    def _assess_threat(
        self,
        turn: Turn,
        *,
        breakout: bool = False,
        local_squad_contact: bool = False,
    ) -> ThreatAssessment:
        core = turn.core
        if core is None:
            return ThreatAssessment(
                lifecycle=LifecycleMode.RESPAWNING,
                primary_reason="CORE_RESPAWNING",
            )

        visible_combat_enemies = tuple(
            enemy
            for enemy in turn.visible_enemies
            if getattr(enemy, "kind") != "CORE"
            and enemy.unit_type in {UnitType.VANGUARD, UnitType.RANGER}
        )
        near_core_enemy_ids = frozenset(
            enemy.id
            for enemy in visible_combat_enemies
            if _distance(core.position, enemy.position)
            <= CORE_EVADE_TRIGGER_DISTANCE
        )
        threatening_core_enemy_ids = frozenset(
            enemy.id
            for enemy in _core_threatening_enemies(
                core.position,
                visible_combat_enemies,
                self.known_obstacles,
            )
        )
        recent_attack = turn.tick <= self.recent_attack_until_tick
        recent_core_attack = turn.tick <= self.recent_core_attack_until_tick
        disengaging = turn.tick <= self.squad_disengage_until_tick
        caution = turn.tick <= self.threat_caution_until_tick

        if self.compatibility_hold:
            lifecycle = LifecycleMode.COMPATIBILITY_HOLD
        elif self.recovery_mode:
            lifecycle = LifecycleMode.RECOVERY
        else:
            lifecycle = LifecycleMode.ACTIVE

        if breakout:
            level = ThreatLevel.BREAKOUT
            primary_reason = "MULTI_AXIS_BREAKOUT"
        elif recent_core_attack:
            level = ThreatLevel.ENGAGED
            primary_reason = "RECENT_CORE_ATTACK"
        elif local_squad_contact:
            level = ThreatLevel.ENGAGED
            primary_reason = "LOCAL_SQUAD_CONTACT"
        elif recent_attack:
            level = ThreatLevel.ENGAGED
            primary_reason = "RECENT_FLEET_ATTACK"
        elif threatening_core_enemy_ids:
            level = ThreatLevel.ENGAGED
            primary_reason = "CURRENT_CORE_ATTACK"
        elif self.pursuing_enemy_ids:
            level = ThreatLevel.PRE_EVADE
            primary_reason = "CONFIRMED_PURSUIT"
        elif self.preemptive_evade_enemy_ids:
            level = ThreatLevel.PRE_EVADE
            primary_reason = "TIME_TO_RANGE"
        elif near_core_enemy_ids:
            level = ThreatLevel.PRE_EVADE
            primary_reason = "CORE_DISTANCE_FALLBACK"
        elif self.active_enemy_ids:
            level = ThreatLevel.ALERT
            primary_reason = "HOSTILE_ACTIVITY"
        elif disengaging:
            level = ThreatLevel.ALERT
            primary_reason = "SQUAD_DISENGAGING"
        else:
            level = ThreatLevel.NORMAL
            primary_reason = "NONE"

        return ThreatAssessment(
            lifecycle=lifecycle,
            level=level,
            primary_reason=primary_reason,
            recent_attack=recent_attack,
            recent_core_attack=recent_core_attack,
            activity_enemy_ids=frozenset(self.active_enemy_ids),
            preemptive_enemy_ids=frozenset(self.preemptive_evade_enemy_ids),
            pursuing_enemy_ids=frozenset(self.pursuing_enemy_ids),
            near_core_enemy_ids=near_core_enemy_ids,
            threatening_core_enemy_ids=threatening_core_enemy_ids,
            disengaging=disengaging,
            local_squad_contact=local_squad_contact,
            caution=caution,
            breakout=breakout,
        )

    def _refresh_threat_assessment(
        self,
        turn: Turn,
        *,
        breakout: bool = False,
        local_squad_contact: bool = False,
    ) -> None:
        self.threat_assessment = self._assess_threat(
            turn,
            breakout=breakout,
            local_squad_contact=local_squad_contact,
        )
        self.combat_pressure_active = self.threat_assessment.combat_pressure

    def _remembered_retreat_threats(
        self,
        turn: Turn,
        visible_enemies: Sequence[object],
    ) -> tuple[RememberedThreat, ...]:
        visible_ids = {enemy.id for enemy in visible_enemies}
        remembered = {
            threat.id: threat
            for threat in self.recent_attack_threats.values()
            if threat.id not in visible_ids and threat.expires_tick >= turn.tick
        }
        tracked_ids = (
            self.active_enemy_ids
            | self.preemptive_evade_enemy_ids
            | self.pursuing_enemy_ids
        )
        for unit_id in tracked_ids - visible_ids - set(remembered):
            motion = self.enemy_unit_motion.get(unit_id)
            if motion is None:
                continue
            remembered[unit_id] = RememberedThreat(
                id=unit_id,
                position=motion.position,
                unit_type=motion.unit_type,
                expires_tick=max(
                    motion.activity_until_tick,
                    motion.preemptive_evade_until_tick,
                    turn.tick,
                ),
            )
        return tuple(
            threat
            for threat in remembered.values()
        )

    @staticmethod
    def _has_imminent_cargo(turn: Turn) -> bool:
        if turn.core is None:
            return False
        return any(
            worker.cargo > 0
            and _distance(worker.position, turn.core.position) <= CORE_SHORT_CARGO_ETA
            for worker in turn.workers
        )

    def _refresh_healing_defenders(
        self,
        turn: Turn,
        combat_target: object | None,
    ) -> None:
        core = turn.core
        defenders = (*turn.vanguards, *turn.rangers)
        defender_ids = {defender.id for defender in defenders}
        self.healing_defender_ids.intersection_update(defender_ids)
        for defender in defenders:
            if defender.hp >= _unit_max_hp(defender.unit_type):
                self.healing_defender_ids.discard(defender.id)
        if core is None:
            self.healing_defender_ids.clear()
            return
        defenders_by_id = {defender.id: defender for defender in defenders}
        for defender_id in tuple(self.healing_defender_ids):
            defender = defenders_by_id[defender_id]
            same_type_guard_remains = any(
                other.id != defender_id
                and other.unit_type is defender.unit_type
                for other in defenders
            )
            if defender.position != core.position and not same_type_guard_remains:
                self.healing_defender_ids.discard(defender_id)

        if self.healing_defender_ids:
            return
        if (
            combat_target is not None
            or self.combat_pressure_active
            or core.view.state is not CoreState.NORMAL
            or core.hp < 5
            or self._has_imminent_cargo(turn)
        ):
            return

        candidates = []
        for defender in defenders:
            max_hp = _unit_max_hp(defender.unit_type)
            missing_hp = max_hp - defender.hp
            same_type = [
                unit for unit in defenders if unit.unit_type is defender.unit_type
            ]
            if missing_hp <= 0:
                continue
            if defender.position != core.position and len(same_type) <= 1:
                continue
            if turn.resources < UNIT_HEAL_RESOURCE_RESERVE + missing_hp:
                continue
            candidates.append(
                (
                    int(defender.position != core.position),
                    defender.hp / max_hp,
                    _distance(defender.position, core.position),
                    _uuid_sort_key(defender),
                    defender,
                )
            )
        if candidates:
            self.healing_defender_ids.add(min(candidates)[4].id)

    def _healing_return_ready(self, turn: Turn, defender: object) -> bool:
        core = turn.core
        if core is None or defender.id not in self.healing_defender_ids:
            return False
        missing_hp = _unit_max_hp(defender.unit_type) - defender.hp
        return (
            missing_hp > 0
            and not self.combat_pressure_active
            and core.view.state is CoreState.NORMAL
            and core.hp == 5
            and turn.resources >= UNIT_HEAL_RESOURCE_RESERVE + missing_hp
            and not self._has_imminent_cargo(turn)
        )

    @staticmethod
    def _pursuit_is_confirmed(motion: EnemyUnitMotion) -> bool:
        return motion.pursuit_score > 0 and (
            motion.core_distance <= CORE_EVADE_TRIGGER_DISTANCE
            or motion.pursuit_score >= DISTANT_PURSUIT_SCORE_THRESHOLD
        )

    @staticmethod
    def _attack_range(unit_type: UnitType) -> int:
        return 3 if unit_type is UnitType.RANGER else 1

    def _attack_event_threats(
        self,
        event: object,
        visible_units: Mapping[UUID, object],
        prior_motion: Mapping[UUID, EnemyUnitMotion],
    ) -> tuple[tuple[UUID, Position, UnitType], ...]:
        actor_id = getattr(event, "actor_id", None)
        if actor_id is not None:
            visible_actor = visible_units.get(actor_id)
            if (
                visible_actor is not None
                and visible_actor.unit_type in {UnitType.VANGUARD, UnitType.RANGER}
            ):
                return ((actor_id, visible_actor.position, visible_actor.unit_type),)
            remembered_actor = prior_motion.get(actor_id)
            if (
                remembered_actor is not None
                and remembered_actor.unit_type
                in {UnitType.VANGUARD, UnitType.RANGER}
            ):
                return (
                    (
                        actor_id,
                        remembered_actor.position,
                        remembered_actor.unit_type,
                    ),
                )

        target_position = getattr(event, "position", None)
        candidates: dict[UUID, tuple[UUID, Position, UnitType]] = {}
        for unit_id, motion in prior_motion.items():
            if motion.unit_type not in {UnitType.VANGUARD, UnitType.RANGER}:
                continue
            can_attack = target_position is None or (
                motion.unit_type is UnitType.VANGUARD
                and _distance(motion.position, target_position) == 1
            ) or (
                motion.unit_type is UnitType.RANGER
                and _ranger_can_shoot(
                    motion.position,
                    target_position,
                    self.known_obstacles,
                )
            )
            if can_attack:
                candidates[unit_id] = (
                    unit_id,
                    motion.position,
                    motion.unit_type,
                )
        if candidates:
            return tuple(candidates.values())

        for unit_id, enemy_unit in visible_units.items():
            if enemy_unit.unit_type not in {UnitType.VANGUARD, UnitType.RANGER}:
                continue
            can_attack = target_position is None or (
                enemy_unit.unit_type is UnitType.VANGUARD
                and _distance(enemy_unit.position, target_position) == 1
            ) or (
                enemy_unit.unit_type is UnitType.RANGER
                and _ranger_can_shoot(
                    enemy_unit.position,
                    target_position,
                    self.known_obstacles,
                )
            )
            if can_attack:
                candidates[unit_id] = (
                    unit_id,
                    enemy_unit.position,
                    enemy_unit.unit_type,
                )
        return tuple(candidates.values())

    def _update_enemy_awareness(self, turn: Turn) -> None:
        visible_cores = {
            enemy.id: enemy
            for enemy in turn.visible_enemies
            if getattr(enemy, "kind") == "CORE"
        }
        visible_units = {
            enemy.id: enemy
            for enemy in turn.visible_enemies
            if getattr(enemy, "kind") != "CORE"
        }
        prior_motion = dict(self.enemy_unit_motion)
        if (
            self.core_observer_target_id is not None
            and self.core_observer_target_id not in visible_cores
            and self.core_observer_target_id != self.isolated_core_target_id
        ):
            sighting = self.enemy_core_sightings.get(self.core_observer_target_id)
            if (
                sighting is None
                or turn.tick - sighting.last_tick > CORE_VISIBILITY_GAP_TICKS
            ):
                self._release_core_observer()
        if any(
            enemy.unit_type in {UnitType.VANGUARD, UnitType.RANGER}
            for enemy in visible_units.values()
        ):
            self.threat_caution_until_tick = max(
                self.threat_caution_until_tick,
                turn.tick + POST_THREAT_CAUTION_TICKS,
            )

        hidden_unit_ids = set(self.enemy_unit_sightings) - set(visible_units)
        for unit_id in hidden_unit_ids:
            self.enemy_unit_sightings.pop(unit_id, None)
        self.active_enemy_ids.clear()
        self.preemptive_evade_enemy_ids.clear()
        self.pursuing_enemy_ids.clear()
        for unit_id in set(self.enemy_unit_motion) - set(visible_units):
            motion = self.enemy_unit_motion[unit_id]
            hidden_ticks = turn.tick - motion.last_tick
            if (
                hidden_ticks >= PURSUIT_MEMORY_TTL
                and turn.tick > motion.activity_until_tick
                and turn.tick > motion.preemptive_evade_until_tick
            ):
                self.enemy_unit_motion.pop(unit_id, None)
                continue
            if (
                turn.tick <= motion.activity_until_tick
                and motion.unit_type in {UnitType.VANGUARD, UnitType.RANGER}
            ):
                self.active_enemy_ids.add(unit_id)
            if (
                turn.tick <= motion.preemptive_evade_until_tick
                and motion.unit_type in {UnitType.VANGUARD, UnitType.RANGER}
            ):
                self.preemptive_evade_enemy_ids.add(unit_id)
            if (
                hidden_ticks < PURSUIT_MEMORY_TTL
                and motion.unit_type in {UnitType.VANGUARD, UnitType.RANGER}
                and self._pursuit_is_confirmed(motion)
            ):
                self.pursuing_enemy_ids.add(unit_id)
        for unit_id, enemy_unit in visible_units.items():
            sighting = self.enemy_unit_sightings.get(unit_id)
            if (
                sighting is not None
                and sighting.last_tick == turn.tick - 1
                and sighting.position == enemy_unit.position
            ):
                sighting.last_tick = turn.tick
            else:
                self.enemy_unit_sightings[unit_id] = EnemyCoreSighting(
                    position=enemy_unit.position,
                    first_tick=turn.tick,
                    last_tick=turn.tick,
                )
            core_distance = (
                _distance(turn.core.position, enemy_unit.position)
                if turn.core is not None
                else SIGNED_INT64_MAX
            )
            previous_motion = self.enemy_unit_motion.get(unit_id)
            pursuit_score = 0
            pursuit_ticks = 0
            activity_until_tick = 0
            preemptive_evade_until_tick = 0
            ticks_to_attack_range = None
            movement_delta = None
            movement_observations = 0
            if (
                previous_motion is not None
                and turn.tick - previous_motion.last_tick
                <= PURSUIT_MEMORY_TTL
            ):
                observation_gap = turn.tick - previous_motion.last_tick
                missed_ticks = max(
                    0,
                    observation_gap - 1,
                )
                pursuit_score = max(
                    0,
                    previous_motion.pursuit_score - missed_ticks,
                )
                activity_until_tick = previous_motion.activity_until_tick
                preemptive_evade_until_tick = (
                    previous_motion.preemptive_evade_until_tick
                )
                if previous_motion.position == enemy_unit.position:
                    pursuit_score = 0
                else:
                    if observation_gap == 1:
                        observed_delta = (
                            enemy_unit.position[0] - previous_motion.position[0],
                            enemy_unit.position[1] - previous_motion.position[1],
                        )
                        if abs(observed_delta[0]) + abs(observed_delta[1]) == 1:
                            movement_delta = observed_delta
                            movement_observations = (
                                previous_motion.movement_observations + 1
                                if previous_motion.movement_delta == observed_delta
                                else 1
                            )
                    activity_until_tick = turn.tick + ACTIVE_ENEMY_ALERT_TICKS
                    closed_distance = previous_motion.core_distance - core_distance
                    if closed_distance > 0:
                        pursuit_score = min(
                            PURSUIT_SCORE_MAX,
                            pursuit_score + 2,
                        )
                        remaining_distance = max(
                            0,
                            core_distance - self._attack_range(enemy_unit.unit_type),
                        )
                        ticks_to_attack_range = math.ceil(
                            remaining_distance * observation_gap / closed_distance
                        )
                        if (
                            ticks_to_attack_range
                            <= CORE_PREEMPTIVE_EVADE_HORIZON_TICKS
                        ):
                            preemptive_evade_until_tick = (
                                turn.tick + ACTIVE_ENEMY_ALERT_TICKS
                            )
                    elif core_distance == previous_motion.core_distance:
                        pursuit_score = min(
                            PURSUIT_SCORE_MAX,
                            pursuit_score + 1,
                        )
                    else:
                        pursuit_score = max(0, pursuit_score - 1)
                if pursuit_score > 0:
                    pursuit_ticks = previous_motion.pursuit_ticks + 1
            motion = EnemyUnitMotion(
                position=enemy_unit.position,
                last_tick=turn.tick,
                core_distance=core_distance,
                unit_type=enemy_unit.unit_type,
                movement_delta=movement_delta,
                movement_observations=movement_observations,
                pursuit_score=pursuit_score,
                pursuit_ticks=pursuit_ticks,
                activity_until_tick=activity_until_tick,
                preemptive_evade_until_tick=preemptive_evade_until_tick,
                ticks_to_attack_range=ticks_to_attack_range,
            )
            self.enemy_unit_motion[unit_id] = motion
            if (
                enemy_unit.unit_type in {UnitType.VANGUARD, UnitType.RANGER}
                and turn.tick <= motion.activity_until_tick
            ):
                self.active_enemy_ids.add(unit_id)
            if (
                enemy_unit.unit_type in {UnitType.VANGUARD, UnitType.RANGER}
                and turn.tick <= motion.preemptive_evade_until_tick
            ):
                self.preemptive_evade_enemy_ids.add(unit_id)
            if (
                enemy_unit.unit_type in {UnitType.VANGUARD, UnitType.RANGER}
                and self._pursuit_is_confirmed(motion)
            ):
                self.pursuing_enemy_ids.add(unit_id)

        core_respawned = any(
            event.event_type == "CORE_RESPAWNED" for event in turn.events
        )
        attack_events = tuple(
            event
            for event in turn.events
            if not core_respawned
            and event.reason_code == "ATTACK"
            and event.event_type in {"CORE_DAMAGED", "UNIT_DAMAGED"}
        )
        if attack_events:
            attack_expires_tick = turn.tick + RECENT_ATTACK_MEMORY_TICKS - 1
            self.recent_attack_until_tick = max(
                self.recent_attack_until_tick,
                attack_expires_tick,
            )
            if any(event.event_type == "CORE_DAMAGED" for event in attack_events):
                self.recent_core_attack_until_tick = max(
                    self.recent_core_attack_until_tick,
                    attack_expires_tick,
                )
            self.threat_caution_until_tick = max(
                self.threat_caution_until_tick,
                self.recent_attack_until_tick,
            )
            for event in attack_events:
                for unit_id, position, unit_type in self._attack_event_threats(
                    event,
                    visible_units,
                    prior_motion,
                ):
                    self.recent_attack_threats[unit_id] = RememberedThreat(
                        id=unit_id,
                        position=position,
                        unit_type=unit_type,
                        expires_tick=attack_expires_tick,
                    )
        else:
            for unit_id, remembered in tuple(self.recent_attack_threats.items()):
                visible = visible_units.get(unit_id)
                if visible is not None:
                    self.recent_attack_threats[unit_id] = RememberedThreat(
                        id=unit_id,
                        position=visible.position,
                        unit_type=visible.unit_type,
                        expires_tick=remembered.expires_tick,
                    )
        for unit_id, remembered in tuple(self.recent_attack_threats.items()):
            if remembered.expires_tick < turn.tick:
                self.recent_attack_threats.pop(unit_id, None)

        for core_id, sighting in tuple(self.stationary_core_memory.items()):
            if turn.tick - sighting.last_tick > STATIONARY_CORE_MEMORY_TTL:
                self.stationary_core_memory.pop(core_id, None)
                self.core_observer_candidates.pop(core_id, None)
                if self.isolated_core_target_id == core_id:
                    self._abort_core_raid(
                        turn,
                        "TARGET_MEMORY_EXPIRED",
                        forget_position=True,
                    )

        for core_id, sighting in tuple(self.enemy_core_sightings.items()):
            if (
                core_id not in visible_cores
                and turn.tick - sighting.last_tick > CORE_VISIBILITY_GAP_TICKS
            ):
                self.enemy_core_sightings.pop(core_id, None)

        for core_id, enemy_core in visible_cores.items():
            sighting = self.enemy_core_sightings.get(core_id)
            continuously_visible = (
                sighting is not None
                and sighting.position == enemy_core.position
                and enemy_core.state is CoreState.NORMAL
                and turn.tick - sighting.last_tick - 1 <= CORE_VISIBILITY_GAP_TICKS
            )
            if continuously_visible:
                sighting.last_tick = turn.tick
                sighting.observations += 1
            else:
                self.enemy_core_sightings[core_id] = EnemyCoreSighting(
                    position=enemy_core.position,
                    first_tick=turn.tick,
                    last_tick=turn.tick,
                    observations=1,
                )
                if (
                    enemy_core.state is not CoreState.NORMAL
                    or (
                        sighting is not None
                        and sighting.position != enemy_core.position
                    )
                    or (
                        core_id in self.stationary_core_memory
                        and self.stationary_core_memory[core_id].position
                        != enemy_core.position
                    )
                ):
                    if self.isolated_core_target_id == core_id:
                        self._abort_core_raid(
                            turn,
                            "TARGET_MOVED",
                            forget_position=True,
                        )
                    else:
                        self.stationary_core_memory.pop(core_id, None)
                        self.core_observer_candidates.pop(core_id, None)

            if (
                enemy_core.state is CoreState.NORMAL
                and core_id not in self.core_observer_candidates
            ):
                observer_id = self._infer_core_observer(turn, enemy_core)
                if observer_id is not None:
                    self.core_observer_candidates[core_id] = observer_id
                    if self.core_observer_target_id is None:
                        self.core_observer_target_id = core_id
                        self.core_raid_spotter_id = observer_id

            current_sighting = self.enemy_core_sightings[core_id]
            if (
                enemy_core.state is CoreState.NORMAL
                and current_sighting.observations >= ISOLATED_CORE_CONFIRM_TICKS + 1
            ):
                self.stationary_core_memory[core_id] = EnemyCoreSighting(
                    position=enemy_core.position,
                    first_tick=current_sighting.first_tick,
                    last_tick=turn.tick,
                    observations=current_sighting.observations,
                )

    def _select_isolated_core_target(self, turn: Turn) -> CoreRaidTarget | None:
        core = turn.core
        if core is None or self.recovery_mode:
            if self.recovery_mode:
                self._interrupt_raid_episode(turn, "RECOVERY_MODE")
            self._release_core_raid()
            return None
        for target_id, cooldown_until in tuple(
            self.raid_target_cooldown_until.items()
        ):
            if cooldown_until < turn.tick:
                self.raid_target_cooldown_until.pop(target_id, None)

        visible_cores = {
            enemy.id: enemy
            for enemy in turn.visible_enemies
            if getattr(enemy, "kind") == "CORE"
        }

        if self.isolated_core_target_id is not None:
            living_defender_ids = {
                unit.id for unit in (*turn.vanguards, *turn.rangers)
            }
            raid_ids = self.raid_vanguard_ids | self.raid_ranger_ids
            if raid_ids - living_defender_ids:
                self._abort_core_raid(turn, "MEMBER_LOST")
                return None
            if core.hp < 5 or core.shield < 5:
                self._abort_core_raid(turn, "HOME_CORE_DAMAGED")
                return None

        if self.isolated_core_target_id is not None:
            target_id = self.isolated_core_target_id
            remembered = self.stationary_core_memory.get(target_id)
            visible_target = visible_cores.get(target_id)
            if (
                remembered is None
                or turn.tick - remembered.last_tick > CORE_RAID_MEMORY_TTL
            ):
                self._abort_core_raid(
                    turn,
                    "TARGET_MEMORY_EXPIRED",
                    forget_position=True,
                )
                return None
            if visible_target is not None and (
                visible_target.state is not CoreState.NORMAL
                or visible_target.position != self.raid_target_position
            ):
                self._abort_core_raid(
                    turn,
                    "TARGET_MOVED",
                    forget_position=True,
                )
                return None
            abort_reason = self._advance_core_raid(
                turn,
                remembered.position,
                visible_target,
            )
            if abort_reason is not None:
                self._abort_core_raid(
                    turn,
                    abort_reason,
                    forget_position=abort_reason == "TARGET_MOVED",
                )
                return None
            vanguards = tuple(
                unit
                for unit in turn.vanguards
                if unit.id in self.raid_vanguard_ids
            )
            rangers = tuple(
                unit for unit in turn.rangers if unit.id in self.raid_ranger_ids
            )
            if (
                not vanguards
                or not rangers
                or _core_raid_strike_distance(
                    remembered.position,
                    vanguards,
                    rangers,
                )
                > CORE_RAID_STRIKE_RELEASE_DISTANCE
            ):
                self._abort_core_raid(turn, "FORMATION_SEPARATED")
                return None
            if visible_target is None and any(
                _distance(defender.position, remembered.position) <= 1
                for defender in (*vanguards, *rangers)
            ):
                self._complete_core_raid(turn)
                return None
            return CoreRaidTarget(
                id=target_id,
                position=remembered.position,
                visible_enemy=visible_target,
            )

        if core.hp < 5 or core.shield < 5:
            return None
        if turn.resource_space < ISOLATED_CORE_MIN_RESOURCE_SPACE:
            return None
        self._clear_completed_raid_rebuild(turn)
        if any(self._raid_rebuild_missing(turn)):
            return None
        if self.squad_return_ids:
            return None

        candidates = []
        for enemy_core in visible_cores.values():
            sighting = self.enemy_core_sightings.get(enemy_core.id)
            if sighting is None:
                continue
            if enemy_core.state is not CoreState.NORMAL:
                continue
            if self.raid_target_cooldown_until.get(enemy_core.id, -1) >= turn.tick:
                continue
            remembered = self.stationary_core_memory.get(enemy_core.id)
            confirmed_at_same_position = (
                remembered is not None
                and remembered.position == enemy_core.position
            )
            if (
                sighting.observations < ISOLATED_CORE_CONFIRM_TICKS + 1
                and not confirmed_at_same_position
            ):
                continue
            selected_groups = self._select_raid_groups(
                turn,
                enemy_core.position,
            )
            if selected_groups is None:
                continue
            vanguard_strike_group, ranger_strike_group = selected_groups
            strike_distance = _core_raid_strike_distance(
                enemy_core.position,
                vanguard_strike_group,
                ranger_strike_group,
            )
            if strike_distance > CORE_RAID_STRIKE_MAX_DISTANCE:
                continue
            candidates.append(
                (
                    strike_distance,
                    _distance(core.position, enemy_core.position),
                    _uuid_sort_key(enemy_core),
                    enemy_core,
                )
            )

        if not candidates:
            return None
        target = min(candidates)[3]
        if not self._initialize_core_raid(turn, target):
            return None
        observer_id = self.core_observer_candidates.get(target.id)
        living_empty_workers = {
            worker.id
            for worker in turn.workers
            if worker.cargo == 0
        }
        self.core_observer_target_id = target.id
        self.core_raid_spotter_id = (
            observer_id if observer_id in living_empty_workers else None
        )
        if self.active_raid_episode is not None:
            self.active_raid_episode.spotter_id = self.core_raid_spotter_id
        return CoreRaidTarget(
            id=target.id,
            position=target.position,
            visible_enemy=target,
        )

    def _stationary_enemy_units(self, turn: Turn) -> tuple[object, ...]:
        units = []
        for enemy in turn.visible_enemies:
            if getattr(enemy, "kind") == "CORE":
                continue
            sighting = self.enemy_unit_sightings.get(enemy.id)
            if (
                sighting is not None
                and sighting.position == enemy.position
                and sighting.last_tick == turn.tick
                and turn.tick - sighting.first_tick >= STATIC_WORKER_CONFIRM_TICKS
            ):
                units.append(enemy)
        return tuple(units)

    def _select_stationary_unit_target(
        self,
        turn: Turn,
        stationary_units: Sequence[object],
    ) -> object | None:
        self.stationary_unit_target_id = None
        core = turn.core
        if (
            core is None
            or self.recovery_mode
            or core.hp < 5
            or core.shield < 5
            or len(turn.vanguards) < STATIC_WORKER_CLEAR_VANGUARDS
            or len(turn.rangers) < STATIC_WORKER_CLEAR_RANGERS
        ):
            return None
        candidates = [
            unit
            for unit in stationary_units
            if _distance(core.position, unit.position)
            <= STATIC_WORKER_CLEAR_MAX_DISTANCE
            and not any(
                getattr(other, "kind") != "CORE"
                and other.id != unit.id
                and other.unit_type in {UnitType.VANGUARD, UnitType.RANGER}
                and _distance(other.position, unit.position) <= CORE_PROTECTOR_RADIUS
                for other in turn.visible_enemies
            )
        ]
        if not candidates:
            return None
        target = min(
            candidates,
            key=lambda unit: (
                0
                if unit.unit_type is UnitType.RANGER
                else 1
                if unit.unit_type is UnitType.WORKER
                else 2,
                _distance(core.position, unit.position),
                min(
                    _distance(defender.position, unit.position)
                    for defender in (*turn.vanguards, *turn.rangers)
                ),
                _uuid_sort_key(unit),
            ),
        )
        self.stationary_unit_target_id = target.id
        return target

    def _enter_recovery(self, tick: int, reason: str) -> None:
        self.recovery_until_tick = max(
            self.recovery_until_tick,
            tick + RECOVERY_TICKS,
        )
        self.recovery_reason = reason
        # Coordinates remembered before destruction are not useful at the new spawn.
        self.resource_last_seen.clear()
        self.resource_intents.clear()
        self.resource_progress.clear()
        self.resource_cooldowns.clear()
        self.scout_target_last_visited.clear()
        self.scout_claims.clear()
        self.scout_active_chunks.clear()
        self.scout_chunk_last_seen.clear()
        self.enemy_unit_sightings.clear()
        self.enemy_unit_motion.clear()
        self.active_enemy_ids.clear()
        self.preemptive_evade_enemy_ids.clear()
        self.pursuing_enemy_ids.clear()
        self.recent_attack_until_tick = 0
        self.recent_core_attack_until_tick = 0
        self.recent_attack_threats.clear()
        self.squad_return_ids.clear()
        self.scout_return_ids.clear()
        self.scout_cooldown_until.clear()
        self.squad_disengage_until_tick = 0

    def _update_recovery_mode(self, turn: Turn) -> None:
        if turn.core is None:
            return
        respawned = any(
            event.event_type == "CORE_RESPAWNED"
            for event in turn.events
        )
        recovery_worker_goal = min(RECOVERY_MIN_WORKERS, self.worker_target)
        distant_low_stock = (
            len(turn.workers) < recovery_worker_goal
            and turn.resources < RECOVERY_INFERENCE_RESOURCE_LIMIT
            and _distance(turn.core.position, turn.beacon.position) >= 80
        )
        if respawned or (distant_low_stock and not self.recovery_mode):
            reason = "CORE_RESPAWNED" if respawned else "REMOTE_LOW_FLEET"
            self._interrupt_raid_episode(turn, reason)
            self._enter_recovery(
                turn.tick,
                reason,
            )
            return
        if not self.recovery_mode:
            return
        nearest_threat = min(
            (
                _distance(turn.core.position, enemy.position)
                for enemy in turn.visible_enemies
                if getattr(enemy, "kind", None) != "CORE"
                and getattr(enemy, "unit_type", None)
                in {UnitType.VANGUARD, UnitType.RANGER}
            ),
            default=None,
        )
        if (
            turn.tick >= self.recovery_until_tick
            and len(turn.workers) >= recovery_worker_goal
            and len(turn.vanguards) >= EARLY_DEFENSE_VANGUARD_TARGET
            and len(turn.rangers) >= EARLY_DEFENSE_RANGER_TARGET
            and turn.resources
            >= min(RECOVERY_MIN_RESOURCES, turn.resource_capacity)
            and (
                nearest_threat is None
                or nearest_threat > RECOVERY_THREAT_DISTANCE
            )
        ):
            self.recovery_until_tick = 0
            self.recovery_reason = "NONE"

    def _update_core_movement_history(self, turn: Turn) -> None:
        for event in turn.events:
            if event.event_type == "CORE_MOVE_SUCCEEDED":
                self.last_core_move_tick = turn.tick
                self.active_core_move_reason = None
            elif event.event_type in {
                "CORE_MOVE_FAILED",
                "CORE_MOVE_CANCELLED",
            }:
                self.last_core_move_tick = turn.tick
                self.last_retreat_direction = None
                self.active_core_move_reason = None

    def _refresh_resource_memory(self, turn: Turn) -> None:
        current_resources = set(turn.resource_cells)
        for cell in current_resources:
            self.resource_last_seen[cell] = turn.tick

        for cell, last_seen in tuple(self.resource_last_seen.items()):
            expired = turn.tick - last_seen > RESOURCE_MEMORY_TTL
            definitely_visible = _cell_visible_to_friendly(
                turn,
                cell,
                self.known_obstacles,
            )
            if expired or (definitely_visible and cell not in current_resources):
                self.resource_last_seen.pop(cell, None)

        living_worker_ids = {worker.id for worker in turn.workers}
        for worker_id, target in tuple(self.resource_intents.items()):
            if (
                worker_id not in living_worker_ids
                or target not in self.resource_last_seen
            ):
                self.resource_intents.pop(worker_id, None)

    def _refresh_resource_progress(
        self,
        workers: Sequence[object],
        *,
        tick: int,
        blocked: set[Position],
    ) -> None:
        self.last_released_targets.clear()
        worker_by_id = {worker.id: worker for worker in workers}

        for key, retry_at_tick in tuple(self.resource_cooldowns.items()):
            worker_id, target = key
            if (
                retry_at_tick <= tick
                or worker_id not in worker_by_id
                or target not in self.resource_last_seen
            ):
                self.resource_cooldowns.pop(key, None)

        for worker_id in tuple(self.resource_progress):
            target = self.resource_intents.get(worker_id)
            if worker_id not in worker_by_id or target not in self.resource_last_seen:
                self.resource_progress.pop(worker_id, None)

        for worker_id, worker in worker_by_id.items():
            target = self.resource_intents.get(worker_id)
            if target is None or target not in self.resource_last_seen:
                continue
            cost = _estimated_path_cost(worker.position, target, blocked)
            progress = self.resource_progress.get(worker_id)
            if progress is None or progress.target != target:
                self.resource_progress[worker_id] = ResourceProgress(target, cost)
                continue
            if cost < progress.best_cost:
                progress.best_cost = cost
                progress.stalled_turns = 0
                continue

            progress.stalled_turns += 1
            if progress.stalled_turns < RESOURCE_STALL_TICKS:
                continue
            self.resource_cooldowns[(worker_id, target)] = (
                tick + RESOURCE_COOLDOWN_TICKS
            )
            self.resource_intents.pop(worker_id, None)
            self.resource_progress.pop(worker_id, None)
            self.last_released_targets[worker_id] = target

    def _assign_resource_targets(
        self,
        workers: Sequence[object],
        *,
        tick: int,
        blocked: set[Position],
        core_position: Position,
    ) -> dict[UUID, Position]:
        available_resources = {
            cell for cell in self.resource_last_seen if cell not in blocked
        }
        if not workers or not available_resources:
            self.resource_intents = {}
            return {}

        ordered_workers = sorted(workers, key=_uuid_sort_key)
        ordered_resources = sorted(available_resources)
        unassigned_cost = PATH_COST_UNREACHABLE * (len(ordered_workers) + 1)
        forbidden_cost = unassigned_cost * 2
        cost_matrix: list[list[int]] = []
        for worker in ordered_workers:
            row = []
            for cell in ordered_resources:
                if self.resource_cooldowns.get((worker.id, cell), 0) > tick:
                    row.append(forbidden_cost)
                    continue
                path_cost = _estimated_path_cost(worker.position, cell, blocked)
                return_cost = _estimated_path_cost(cell, core_position, blocked)
                if (
                    path_cost >= PATH_COST_UNREACHABLE
                    or return_cost >= PATH_COST_UNREACHABLE
                ):
                    row.append(forbidden_cost)
                    continue
                age = tick - self.resource_last_seen[cell]
                stale_penalty = 0 if age == 0 else min(6, 2 + age // 8)
                sticky_bonus = (
                    RESOURCE_ASSIGNMENT_STICKY_BONUS
                    if self.resource_intents.get(worker.id) == cell
                    else 0
                )
                row.append(
                    max(
                        0,
                        path_cost
                        + return_cost
                        + stale_penalty
                        - sticky_bonus,
                    )
                )
            row.extend([unassigned_cost] * len(ordered_workers))
            cost_matrix.append(row)

        assignments: dict[UUID, Position] = {}
        for row_index, (worker, column_index) in enumerate(
            zip(
                ordered_workers,
                _minimum_cost_assignment(cost_matrix),
                strict=True,
            )
        ):
            if column_index >= len(ordered_resources):
                continue
            if cost_matrix[row_index][column_index] >= forbidden_cost:
                continue
            assignments[worker.id] = ordered_resources[column_index]

        self.resource_intents = assignments
        return assignments

    def _set_worker_mode(
        self,
        worker: object,
        mode: str,
        target: Position | None = None,
    ) -> None:
        self.worker_modes[worker.id] = mode
        if target is None:
            self.worker_targets.pop(worker.id, None)
        else:
            self.worker_targets[worker.id] = target

    def _refresh_scout_assignments(self, workers: Sequence[object]) -> None:
        living_ids = {getattr(worker, "id") for worker in workers}
        for worker_id in set(self.scout_slots) - living_ids:
            self.scout_slots.pop(worker_id, None)
            self.scout_stages.pop(worker_id, None)
            self.scout_progress.pop(worker_id, None)
            self.scout_active_chunks.pop(worker_id, None)
            self.worker_history.pop(worker_id, None)

        used_slots = set(self.scout_slots.values())
        for worker in workers:
            worker_id = getattr(worker, "id")
            if worker_id in self.scout_slots:
                continue
            slot = 0
            while slot in used_slots:
                slot += 1
            self.scout_slots[worker_id] = slot
            self.scout_stages[worker_id] = 0
            used_slots.add(slot)

    def _scout_chunk_waypoint(
        self,
        worker_id: UUID,
        chunk: Position,
        stage: int | None = None,
    ) -> Position:
        slot = self.scout_slots[worker_id]
        waypoint_index = (
            self.scout_stages[worker_id] if stage is None else stage
        ) % SCOUT_STAGE_CYCLE
        local_x, local_y = SCOUT_SCAN_WAYPOINTS[waypoint_index]
        if slot % 2:
            local_x, local_y = local_y, local_x
        return chunk[0] * 32 + local_x, chunk[1] * 32 + local_y

    def _select_scout_chunk(
        self,
        worker_id: UUID,
        core_position: Position,
        beacon_position: Position | None,
    ) -> Position:
        core_chunk = _chunk_coordinates(core_position)
        claimed_chunks = {
            chunk
            for owner, chunk in self.scout_active_chunks.items()
            if owner != worker_id
        }
        minimum_beacon_distance = None
        if beacon_position is not None and self.beacon_policy != "pursue":
            minimum_beacon_distance = min(
                RETREAT_MIN_BEACON_DISTANCE,
                _distance(core_position, beacon_position),
            )

        candidates: list[Position] = []
        for offset_x, offset_y in SCOUT_CHUNK_OFFSETS:
            chunk = core_chunk[0] + offset_x, core_chunk[1] + offset_y
            if chunk in claimed_chunks:
                continue
            if minimum_beacon_distance is not None and any(
                _distance(
                    self._scout_chunk_waypoint(worker_id, chunk, stage),
                    beacon_position,
                )
                < minimum_beacon_distance
                for stage in range(SCOUT_STAGE_CYCLE)
            ):
                continue
            candidates.append(chunk)

        if not candidates:
            candidates = [
                (core_chunk[0] + offset_x, core_chunk[1] + offset_y)
                for offset_x, offset_y in SCOUT_CHUNK_OFFSETS
                if (core_chunk[0] + offset_x, core_chunk[1] + offset_y)
                not in claimed_chunks
            ]
        if not candidates:
            return core_chunk

        slot = self.scout_slots[worker_id]
        return min(
            candidates,
            key=lambda chunk: (
                self.scout_chunk_last_seen.get(chunk, -1),
                -_chunk_resource_quota(
                    (chunk[0] * 32 + 16, chunk[1] * 32 + 16)
                ),
                _distance(
                    core_position,
                    (chunk[0] * 32 + 16, chunk[1] * 32 + 16),
                ),
                (chunk[0] + chunk[1] - slot) % 2,
                chunk[0],
                chunk[1],
            ),
        )

    def _scout_target(
        self,
        worker_id: UUID,
        core_position: Position,
        beacon_position: Position | None,
        *,
        claim: bool = False,
    ) -> Position:
        chunk = self.scout_active_chunks.get(worker_id)
        if chunk is None:
            chunk = self._select_scout_chunk(
                worker_id,
                core_position,
                beacon_position,
            )
            self.scout_active_chunks[worker_id] = chunk
            self.scout_stages[worker_id] = 0
        target = self._scout_chunk_waypoint(worker_id, chunk)
        if claim:
            self.scout_claims.add(target)
        return target

    def _advance_scout(
        self,
        worker_id: UUID,
        *,
        visited_target: Position | None = None,
        tick: int | None = None,
    ) -> None:
        if visited_target is not None and tick is not None:
            self.scout_target_last_visited[visited_target] = tick
        stage = self.scout_stages[worker_id]
        if stage + 1 < SCOUT_STAGE_CYCLE:
            self.scout_stages[worker_id] = stage + 1
            return

        completed_chunk = self.scout_active_chunks.pop(worker_id, None)
        if completed_chunk is not None and tick is not None:
            self.scout_chunk_last_seen[completed_chunk] = tick
        self.scout_stages[worker_id] = 0

    def _scout_route_stalled(
        self,
        worker: object,
        target: Position,
        context: MovementContext,
    ) -> bool:
        blocked = (
            set(context.obstacles)
            | set(context.enemy_cells)
            | set(context.danger_cells)
        )
        cost = _estimated_path_cost(worker.position, target, blocked)
        progress = self.scout_progress.get(worker.id)
        if progress is None or progress.target != target:
            self.scout_progress[worker.id] = ScoutProgress(target, cost)
            return False
        if cost < progress.best_cost:
            progress.best_cost = cost
            progress.stalled_turns = 0
            return False
        progress.stalled_turns += 1
        return progress.stalled_turns >= SCOUT_STALL_TICKS

    def _control_empty_worker(
        self,
        worker: object,
        *,
        tick: int,
        core_position: Position,
        beacon_position: Position | None,
        current_resources: set[Position],
        assigned_target: Position | None,
        context: MovementContext,
    ) -> None:
        if (
            assigned_target == worker.position
            and worker.position in current_resources
        ):
            self.scout_progress.pop(worker.id, None)
            worker.harvest()
            self._set_worker_mode(worker, "HARVEST", worker.position)
            return

        if assigned_target is not None:
            self.scout_progress.pop(worker.id, None)
            if _queue_toward(
                worker,
                assigned_target,
                context,
                allow_target_entry=True,
                discouraged=set(self.worker_history[worker.id]),
            ):
                self._set_worker_mode(worker, "RESOURCE", assigned_target)
                return
            worker.wait()
            self._set_worker_mode(worker, "RESOURCE_BLOCKED", assigned_target)
            return

        target = self._scout_target(
            worker.id,
            core_position,
            beacon_position,
            claim=True,
        )
        if worker.position == target:
            self.scout_progress.pop(worker.id, None)
            self._advance_scout(
                worker.id,
                visited_target=target,
                tick=tick,
            )
            target = self._scout_target(
                worker.id,
                core_position,
                beacon_position,
                claim=True,
            )
        elif self._scout_route_stalled(worker, target, context):
            self.scout_progress.pop(worker.id, None)
            self._advance_scout(worker.id, tick=tick)
            target = self._scout_target(
                worker.id,
                core_position,
                beacon_position,
                claim=True,
            )
        if not _queue_toward(
            worker,
            target,
            context,
            discouraged=set(self.worker_history[worker.id]),
        ):
            self._advance_scout(worker.id, tick=tick)
            target = self._scout_target(
                worker.id,
                core_position,
                beacon_position,
                claim=True,
            )
            moved = _queue_toward(
                worker,
                target,
                context,
                discouraged=set(self.worker_history[worker.id]),
            )
            if not moved:
                worker.wait()
                self._set_worker_mode(worker, "SCOUT_BLOCKED", target)
                return
        self._set_worker_mode(worker, "SCOUT", target)

    def _core_observer_position(
        self,
        turn: Turn,
        raid_target: CoreRaidTarget | None,
    ) -> Position | None:
        if self.core_raid_spotter_id is None:
            return None
        worker = next(
            (
                candidate
                for candidate in turn.workers
                if candidate.id == self.core_raid_spotter_id
            ),
            None,
        )
        if worker is None or worker.cargo > 0:
            self._release_core_observer()
            return None
        if raid_target is not None:
            return raid_target.position
        target_id = self.core_observer_target_id
        sighting = (
            self.enemy_core_sightings.get(target_id)
            if target_id is not None
            else None
        )
        if (
            sighting is None
            or sighting.observations >= ISOLATED_CORE_CONFIRM_TICKS + 1
        ):
            self._release_core_observer()
            return None
        return sighting.position

    def _control_core_observer(
        self,
        worker: object,
        target: Position,
        context: MovementContext,
    ) -> None:
        current_distance = _distance(worker.position, target)
        if (
            CORE_OBSERVER_MIN_DISTANCE
            <= current_distance
            <= CORE_OBSERVER_MAX_DISTANCE
            and worker.position not in context.danger_cells
            and _has_vision_line(worker.position, target, context.obstacles)
        ):
            worker.wait()
            self._set_worker_mode(worker, "CORE_OBSERVER", target)
            return

        candidates = []
        for dx in range(-CORE_OBSERVER_MAX_DISTANCE, CORE_OBSERVER_MAX_DISTANCE + 1):
            for dy in range(
                -CORE_OBSERVER_MAX_DISTANCE,
                CORE_OBSERVER_MAX_DISTANCE + 1,
            ):
                watch_position = (target[0] + dx, target[1] + dy)
                watch_distance = abs(dx) + abs(dy)
                if (
                    not CORE_OBSERVER_MIN_DISTANCE
                    <= watch_distance
                    <= CORE_OBSERVER_MAX_DISTANCE
                    or not _is_signed_int64_position(watch_position)
                    or watch_position in context.obstacles
                    or watch_position in context.enemy_cells
                    or watch_position in context.danger_cells
                    or watch_position == context.core_position
                    or not _observer_can_see(
                        watch_position,
                        target,
                        CORE_OBSERVER_MAX_DISTANCE,
                        context.obstacles,
                    )
                ):
                    continue
                candidates.append(
                    (
                        _distance(worker.position, watch_position),
                        CORE_OBSERVER_MAX_DISTANCE - watch_distance,
                        watch_position[0],
                        watch_position[1],
                        watch_position,
                    )
                )
        if candidates:
            watch_position = min(candidates)[4]
            if _queue_toward(worker, watch_position, context):
                self._set_worker_mode(
                    worker,
                    "CORE_OBSERVER_REPOSITION",
                    target,
                )
                return
        worker.wait()
        self._set_worker_mode(worker, "CORE_OBSERVER_BLOCKED", target)

    def choose_actions(self, turn: Turn) -> None:
        turn.clear()
        if turn.core is None:
            self._interrupt_raid_episode(turn, "CORE_LOST")
            self._refresh_threat_assessment(turn)
            return

        core = turn.core
        if self.startup_tick is None:
            self.startup_tick = turn.tick
        self._refresh_return_states(turn)
        self._refresh_raid_episode(turn)
        self._update_recovery_mode(turn)
        self._update_core_movement_history(turn)
        self._update_enemy_awareness(turn)
        self._refresh_compatibility_hold()
        self.known_obstacles.update(turn.obstacle_cells)
        self._refresh_threat_assessment(turn)
        self.stationary_unit_target_id = None
        active_raid_target = self._active_raid_target_for_recall()
        home_defense_pressure = self._home_defense_pressure()
        if home_defense_pressure and active_raid_target is not None:
            self._abort_core_raid(turn, "HOME_DEFENSE")
        if self.compatibility_hold:
            self._interrupt_raid_episode(turn, "COMPATIBILITY_HOLD")
            self._release_core_raid()
            self._release_core_observer()
        if self.compatibility_hold or home_defense_pressure:
            isolated_core_target = None
        else:
            isolated_core_target = self._select_isolated_core_target(turn)
        stationary_unit_target = None
        if (
            not self.compatibility_hold
            and not home_defense_pressure
            and isolated_core_target is None
        ):
            stationary_candidates = self._stationary_enemy_units(turn)
            stationary_unit_target = self._select_stationary_unit_target(
                turn,
                stationary_candidates,
            )
        combat_target = isolated_core_target or stationary_unit_target
        observer_position = self._core_observer_position(
            turn,
            isolated_core_target,
        )
        enemies = tuple(turn.visible_enemies)
        mobile_enemies = tuple(
            enemy
            for enemy in enemies
            if getattr(enemy, "kind") != "CORE"
            and enemy.unit_type in {UnitType.VANGUARD, UnitType.RANGER}
        )
        if self._strike_group_locally_threatened(
            turn,
            combat_target,
            mobile_enemies,
        ):
            if isinstance(combat_target, CoreRaidTarget):
                self._abort_core_raid(turn, "LOCAL_SUPERIORITY_LOST")
            else:
                self._recall_strike_group(turn, combat_target)
                self._release_core_raid()
            self._release_core_observer()
            self.stationary_unit_target_id = None
            combat_target = None
            observer_position = None
            self._refresh_threat_assessment(
                turn,
                local_squad_contact=True,
            )
        enemy_cells = {enemy.position for enemy in enemies}
        danger_cells = _enemy_threat_cells(enemies, self.known_obstacles)
        self.last_danger_cells = danger_cells
        discouraged_core_cells = {
            (
                sighting.position[0] + dx,
                sighting.position[1] + dy,
            )
            for sighting in self.stationary_core_memory.values()
            for dx in range(-1, 2)
            for dy in range(-1, 2)
            if abs(dx) + abs(dy) <= 1
        }
        friendly_counts = Counter(unit.position for unit in turn.units)
        friendly_counts[core.position] += 1
        context = MovementContext(
            obstacles=set(self.known_obstacles),
            resource_cells=set(turn.resource_cells),
            enemy_cells=enemy_cells,
            danger_cells=danger_cells,
            discouraged_cells=discouraged_core_cells,
            friendly_counts=friendly_counts,
            reserved_destinations=set(),
            core_position=core.position,
            preplanned_units=set(),
        )
        context.delivery_lane = _select_delivery_lane(context)

        workers = sorted(turn.workers, key=_uuid_sort_key)
        self.worker_modes.clear()
        self.worker_targets.clear()
        self.scout_claims.clear()
        for chunk, last_seen in tuple(self.scout_chunk_last_seen.items()):
            if turn.tick - last_seen > SCOUT_COVERAGE_MEMORY_TTL:
                self.scout_chunk_last_seen.pop(chunk, None)
        self._refresh_scout_assignments(workers)
        for worker in workers:
            history = self.worker_history.setdefault(
                worker.id,
                deque(maxlen=6),
            )
            if not history or history[-1] != worker.position:
                history.append(worker.position)
        cargo_workers = [worker for worker in workers if worker.cargo > 0]
        cargo_workers.sort(
            key=lambda worker: (
                _distance(worker.position, core.position),
                _uuid_sort_key(worker),
            )
        )
        empty_workers = [worker for worker in workers if worker.cargo == 0]
        self._refresh_healing_defenders(turn, combat_target)
        healing_holds = {
            defender.id
            for defender in (*turn.vanguards, *turn.rangers)
            if self._healing_return_ready(turn, defender)
        }
        observer_id = (
            self.core_raid_spotter_id
            if observer_position is not None
            else None
        )
        economic_empty_workers = [
            worker for worker in empty_workers if worker.id != observer_id
        ]
        preplanned_units = _queue_core_defender_egress(
            turn,
            context,
            mobile_enemies,
            healing_holds,
        )
        preplanned_units.update(_queue_core_delivery_handoff(turn, context))
        context.preplanned_units = preplanned_units
        for worker in workers:
            if worker.id not in preplanned_units:
                continue
            if worker.position == core.position:
                mode = "CLEAR_CORE_HANDOFF"
            elif worker.cargo > 0:
                mode = "DELIVERY_CHAIN_CARGO"
            else:
                mode = "DELIVERY_CHAIN_CLEAR"
            self._set_worker_mode(worker, mode, core.position)
        self._refresh_resource_memory(turn)
        resource_route_blocked = (
            set(context.obstacles)
            | set(context.enemy_cells)
            | set(context.danger_cells)
        )
        self._refresh_resource_progress(
            economic_empty_workers,
            tick=turn.tick,
            blocked=resource_route_blocked,
        )
        resource_assignments = self._assign_resource_targets(
            economic_empty_workers,
            tick=turn.tick,
            blocked=resource_route_blocked,
            core_position=core.position,
        )
        current_resources = set(turn.resource_cells)
        departing_core_workers = [
            worker for worker in empty_workers if worker.position == core.position
        ]
        departing_ids = {worker.id for worker in departing_core_workers}

        navigation_beacon = turn.beacon.position
        for worker in departing_core_workers:
            if worker.id in preplanned_units:
                continue
            if self._control_returning_scout(
                turn,
                worker,
                mobile_enemies,
                context,
            ):
                continue
            if _queue_away_from_enemies(
                worker,
                mobile_enemies,
                context,
                turn.beacon.position,
            ):
                if _distance(worker.position, core.position) > SCOUT_SAFE_RETURN_RADIUS:
                    self.scout_return_ids.add(worker.id)
                self._set_worker_mode(worker, "EVADE", core.position)
                continue
            if (
                self.recovery_mode
                and len(workers) < min(RECOVERY_MIN_WORKERS, self.worker_target)
            ):
                recovery_egress = tuple(
                    sorted(
                        _exploration_directions(worker),
                        key=lambda direction: _distance(
                            _destination(worker.position, direction),
                            navigation_beacon,
                        ),
                        reverse=True,
                    )
                )
                if _queue_move(worker, recovery_egress, context):
                    self._set_worker_mode(worker, "RECOVERY_EGRESS", core.position)
                    continue
            if worker.id == observer_id and observer_position is not None:
                self._control_core_observer(
                    worker,
                    observer_position,
                    context,
                )
                continue
            self._control_empty_worker(
                worker,
                tick=turn.tick,
                core_position=core.position,
                beacon_position=navigation_beacon,
                current_resources=current_resources,
                assigned_target=resource_assignments.get(worker.id),
                context=context,
            )

        for worker in cargo_workers:
            if worker.id in preplanned_units:
                continue
            if _queue_away_from_enemies(
                worker,
                mobile_enemies,
                context,
                turn.beacon.position,
            ):
                self._set_worker_mode(worker, "EVADE_CARGO", core.position)
                continue
            if worker.position == core.position:
                if core.view.state is CoreState.NORMAL and turn.resource_space > 0:
                    worker.deposit()
                    self._set_worker_mode(worker, "DEPOSIT", core.position)
                elif core.view.state is not CoreState.NORMAL:
                    worker.wait()
                    self._set_worker_mode(worker, "WAIT_CORE", core.position)
                else:
                    moved = _queue_move(
                        worker,
                        _exploration_directions(worker),
                        context,
                    )
                    if not moved:
                        worker.wait()
                    self._set_worker_mode(
                        worker,
                        "CLEAR_CORE" if moved else "CLEAR_CORE_BLOCKED",
                    )
                continue
            moved = _queue_toward(
                worker,
                core.position,
                context,
                allow_core_entry=True,
                allow_single_friendly_transit=True,
            )
            if not moved:
                worker.wait()
            self._set_worker_mode(
                worker,
                "RETURN" if moved else "RETURN_BLOCKED",
                core.position,
            )

        for worker in empty_workers:
            if worker.id in departing_ids or worker.id in preplanned_units:
                continue
            if self._control_returning_scout(
                turn,
                worker,
                mobile_enemies,
                context,
            ):
                continue
            if _queue_away_from_enemies(
                worker,
                mobile_enemies,
                context,
                turn.beacon.position,
            ):
                if _distance(worker.position, core.position) > SCOUT_SAFE_RETURN_RADIUS:
                    self.scout_return_ids.add(worker.id)
                self._set_worker_mode(worker, "EVADE", core.position)
                continue
            if worker.id == observer_id and observer_position is not None:
                self._control_core_observer(
                    worker,
                    observer_position,
                    context,
                )
                continue
            self._control_empty_worker(
                worker,
                tick=turn.tick,
                core_position=core.position,
                beacon_position=navigation_beacon,
                current_resources=current_resources,
                assigned_target=resource_assignments.get(worker.id),
                context=context,
            )

        for worker_id in tuple(self.scout_progress):
            if self.worker_modes.get(worker_id) not in {"SCOUT", "SCOUT_BLOCKED"}:
                self.scout_progress.pop(worker_id, None)

        planned_damage: dict[UUID, int] = {}
        self._control_vanguards(
            turn,
            mobile_enemies,
            context,
            combat_target,
            planned_damage,
        )
        self._control_rangers(
            turn,
            mobile_enemies,
            context,
            combat_target,
            planned_damage,
        )
        self._control_core(turn, context, combat_target)

    def _strike_group_ids(
        self,
        turn: Turn,
        target: object | None,
    ) -> tuple[set[UUID], set[UUID]]:
        if target is None:
            return set(), set()
        vanguards = sorted(turn.vanguards, key=_uuid_sort_key)
        rangers = sorted(turn.rangers, key=_uuid_sort_key)
        if isinstance(target, CoreRaidTarget):
            if target.id == self.isolated_core_target_id and (
                self.raid_vanguard_ids or self.raid_ranger_ids
            ):
                return (
                    self.raid_vanguard_ids & {unit.id for unit in vanguards},
                    self.raid_ranger_ids & {unit.id for unit in rangers},
                )
            return (
                {
                    unit.id
                    for unit in vanguards[
                        VANGUARD_CORE_GUARDS:DEFENSE_VANGUARD_TARGET
                    ]
                },
                {
                    unit.id
                    for unit in rangers[RANGER_CORE_GUARDS:DEFENSE_RANGER_TARGET]
                },
            )

        ranger_count = min(2, max(1, len(rangers) - 2))
        ranger_strikers = rangers[-ranger_count:]
        remaining_damage = max(0, getattr(target, "hp", 1) - len(ranger_strikers))
        vanguard_count = min(
            max(0, remaining_damage),
            max(1, len(vanguards) - 2),
        )
        return (
            {unit.id for unit in vanguards[-vanguard_count:]}
            if vanguard_count
            else set(),
            {unit.id for unit in ranger_strikers},
        )

    def _refresh_return_states(self, turn: Turn) -> None:
        core = turn.core
        if core is None:
            self.squad_return_ids.clear()
            self.scout_return_ids.clear()
            return
        defenders = {unit.id: unit for unit in (*turn.vanguards, *turn.rangers)}
        self.squad_return_ids.intersection_update(defenders)
        for unit_id in tuple(self.squad_return_ids):
            unit = defenders[unit_id]
            guard_radius = (
                VANGUARD_GUARD_RADIUS
                if unit.unit_type is UnitType.VANGUARD
                else RANGER_GUARD_RADIUS
            )
            local_threat = any(
                getattr(enemy, "kind") != "CORE"
                and enemy.unit_type in {UnitType.VANGUARD, UnitType.RANGER}
                and _distance(unit.position, enemy.position)
                <= UNIT_EVADE_TRIGGER_DISTANCE
                for enemy in turn.visible_enemies
            )
            if (
                not local_threat
                and _distance(unit.position, core.position) <= guard_radius
            ):
                self.squad_return_ids.discard(unit_id)

        worker_ids = {worker.id for worker in turn.workers}
        self.scout_return_ids.intersection_update(worker_ids)
        for worker_id in tuple(self.scout_cooldown_until):
            if (
                worker_id not in worker_ids
                or self.scout_cooldown_until[worker_id] < turn.tick
            ):
                self.scout_cooldown_until.pop(worker_id, None)

    def _recall_strike_group(self, turn: Turn, target: object | None) -> None:
        strike_vanguards, strike_rangers = self._strike_group_ids(turn, target)
        self.squad_return_ids.update(strike_vanguards)
        self.squad_return_ids.update(strike_rangers)
        if self.core_raid_spotter_id is not None:
            self.scout_return_ids.add(self.core_raid_spotter_id)
        self.squad_disengage_until_tick = max(
            self.squad_disengage_until_tick,
            turn.tick + SQUAD_DISENGAGE_TICKS,
        )

    def _active_raid_target_for_recall(self) -> CoreRaidTarget | None:
        target_id = self.isolated_core_target_id
        if target_id is None:
            return None
        remembered = self.stationary_core_memory.get(target_id)
        if remembered is None:
            return None
        return CoreRaidTarget(
            id=target_id,
            position=remembered.position,
            visible_enemy=None,
        )

    def _strike_group_locally_threatened(
        self,
        turn: Turn,
        target: object | None,
        enemies: Sequence[object],
    ) -> bool:
        if target is None:
            return False
        strike_vanguards, strike_rangers = self._strike_group_ids(turn, target)
        strike_ids = strike_vanguards | strike_rangers
        members = [unit for unit in turn.units if unit.id in strike_ids]
        target_id = getattr(target, "id", None)
        local_enemies = tuple(
            enemy
            for enemy in enemies
            if enemy.id != target_id
            and any(
                _distance(member.position, enemy.position)
                <= UNIT_EVADE_TRIGGER_DISTANCE
                for member in members
            )
        )
        if not local_enemies:
            return False
        if isinstance(target, CoreRaidTarget):
            friendly_power = self._combat_power(
                members,
                target.position,
                self.known_obstacles,
            )
            enemy_power = self._combat_power(
                local_enemies,
                target.position,
                self.known_obstacles,
            )
            return friendly_power < enemy_power + CORE_RAID_SUPERIORITY_MARGIN
        return True

    def _control_returning_scout(
        self,
        turn: Turn,
        worker: object,
        enemies: Sequence[object],
        context: MovementContext,
    ) -> bool:
        core = turn.core
        if core is None:
            return False
        nearby_enemies = tuple(
            enemy
            for enemy in enemies
            if _distance(worker.position, enemy.position)
            <= UNIT_EVADE_TRIGGER_DISTANCE
        )
        if nearby_enemies:
            self.scout_cooldown_until.pop(worker.id, None)
            self.scout_return_ids.add(worker.id)
        cooldown_until = self.scout_cooldown_until.get(worker.id, 0)
        if cooldown_until >= turn.tick:
            worker.wait()
            self._set_worker_mode(worker, "SCOUT_COOLDOWN", core.position)
            return True
        if worker.id not in self.scout_return_ids:
            return False
        if nearby_enemies and _queue_away_from_enemies(
            worker,
            nearby_enemies,
            context,
            turn.beacon.position,
        ):
            self._set_worker_mode(worker, "SCOUT_EVADE", core.position)
            return True
        if (
            not nearby_enemies
            and _distance(worker.position, core.position)
            <= SCOUT_SAFE_RETURN_RADIUS
        ):
            self.scout_return_ids.discard(worker.id)
            self.scout_cooldown_until[worker.id] = (
                turn.tick + SCOUT_COOLDOWN_TICKS
            )
            worker.wait()
            self._set_worker_mode(worker, "SCOUT_COOLDOWN", core.position)
            return True
        if _queue_toward(
            worker,
            core.position,
            context,
            allow_core_entry=True,
            allow_single_friendly_transit=True,
            discouraged=set(self.worker_history.get(worker.id, ())),
            discouraged_penalty=SCOUT_RETURN_HISTORY_PENALTY,
        ):
            self._set_worker_mode(worker, "SCOUT_RETURN", core.position)
        else:
            worker.wait()
            self._set_worker_mode(worker, "SCOUT_RETURN_BLOCKED", core.position)
        return True

    def _control_returning_defender(
        self,
        turn: Turn,
        defender: object,
        context: MovementContext,
    ) -> bool:
        if defender.id not in self.squad_return_ids:
            return False
        core = turn.core
        if core is None:
            return False

        guard_radius = (
            VANGUARD_GUARD_RADIUS
            if defender.unit_type is UnitType.VANGUARD
            else RANGER_GUARD_RADIUS
        )
        if _distance(defender.position, core.position) <= guard_radius:
            self.squad_return_ids.discard(defender.id)
            return False

        movement_options = (
            {"avoid_danger": True},
            {"avoid_danger": False},
        )
        for options in movement_options:
            if _queue_toward(
                defender,
                core.position,
                context,
                allow_core_entry=True,
                allow_single_friendly_transit=True,
                **options,
            ):
                return True
        defender.wait()
        return True

    def _control_vanguards(
        self,
        turn: Turn,
        enemies: Sequence[object],
        context: MovementContext,
        isolated_core_target: object | None,
        planned_damage: dict[UUID, int],
    ) -> None:
        core = turn.core
        if core is None:
            return
        target_id = getattr(isolated_core_target, "id", None)
        visible_target = (
            isolated_core_target.visible_enemy
            if isinstance(isolated_core_target, CoreRaidTarget)
            else isolated_core_target
        )
        avoidance_enemies = tuple(
            enemy for enemy in enemies if enemy.id != target_id
        )
        core_threats = _core_threatening_enemies(
            core.position,
            enemies,
            context.obstacles,
        )
        strike_vanguards, _ = self._strike_group_ids(turn, isolated_core_target)
        for index, vanguard in enumerate(
            sorted(turn.vanguards, key=_uuid_sort_key)
        ):
            if context.preplanned_units and vanguard.id in context.preplanned_units:
                continue
            immediate_core_threats = [
                enemy
                for enemy in core_threats
                if _distance(vanguard.position, core.position)
                <= CORE_PROTECTOR_RADIUS
                and _distance(vanguard.position, enemy.position) == 1
            ]
            if immediate_core_threats:
                target = min(
                    immediate_core_threats,
                    key=lambda enemy: _projected_combat_target_key(
                        vanguard.position,
                        enemy,
                        planned_damage,
                    ),
                )
                direction = _direction_to_adjacent(vanguard.position, target.position)
                if direction is not None:
                    vanguard.sweep(direction)
                    _record_planned_cell_damage(
                        target.position,
                        enemies,
                        planned_damage,
                    )
                    continue
            if self._healing_return_ready(turn, vanguard):
                if vanguard.position == core.position:
                    vanguard.heal()
                elif not _queue_toward(
                    vanguard,
                    core.position,
                    context,
                    allow_core_entry=True,
                    allow_single_friendly_transit=True,
                ):
                    vanguard.wait()
                continue
            if self._control_returning_defender(turn, vanguard, context):
                continue
            pursuing_adjacent = [
                enemy
                for enemy in enemies
                if enemy.id in self.pursuing_enemy_ids
                and _distance(vanguard.position, enemy.position) == 1
            ]
            if pursuing_adjacent:
                pursuer = min(
                    pursuing_adjacent,
                    key=lambda enemy: _projected_combat_target_key(
                        vanguard.position,
                        enemy,
                        planned_damage,
                    ),
                )
                direction = _direction_to_adjacent(
                    vanguard.position,
                    pursuer.position,
                )
                if direction is not None:
                    vanguard.sweep(direction)
                    _record_planned_cell_damage(
                        pursuer.position,
                        enemies,
                        planned_damage,
                    )
                    continue
            strike_member = vanguard.id in strike_vanguards
            if strike_member:
                if isinstance(isolated_core_target, CoreRaidTarget):
                    adjacent_opponents = [
                        enemy
                        for enemy in self._raid_local_opponents(turn)
                        if _distance(vanguard.position, enemy.position) == 1
                    ]
                    if adjacent_opponents:
                        opponent = min(
                            adjacent_opponents,
                            key=lambda enemy: _projected_combat_target_key(
                                vanguard.position,
                                enemy,
                                planned_damage,
                            ),
                        )
                        direction = _direction_to_adjacent(
                            vanguard.position,
                            opponent.position,
                        )
                        if direction is not None:
                            vanguard.sweep(direction)
                            _record_planned_cell_damage(
                                opponent.position,
                                enemies,
                                planned_damage,
                            )
                            continue
                if (
                    isinstance(isolated_core_target, CoreRaidTarget)
                    and self.raid_phase is RaidPhase.STAGE
                ):
                    stage_position = self.raid_stage_assignments.get(
                        vanguard.id,
                        isolated_core_target.position,
                    )
                    if (
                        _distance(vanguard.position, stage_position)
                        <= CORE_RAID_STAGE_TOLERANCE
                    ):
                        vanguard.wait()
                    elif not _queue_toward(
                        vanguard,
                        stage_position,
                        context,
                    ):
                        vanguard.wait()
                    continue
                if (
                    isinstance(isolated_core_target, CoreRaidTarget)
                    and self.raid_phase is RaidPhase.BREACH
                ):
                    raid_defenders = self._raid_breach_opponents(
                        turn,
                        isolated_core_target.position,
                    )
                    adjacent_defenders = [
                        enemy
                        for enemy in raid_defenders
                        if _distance(vanguard.position, enemy.position) == 1
                    ]
                    if adjacent_defenders:
                        defender = min(
                            adjacent_defenders,
                            key=lambda enemy: _projected_combat_target_key(
                                vanguard.position,
                                enemy,
                                planned_damage,
                            ),
                        )
                        direction = _direction_to_adjacent(
                            vanguard.position,
                            defender.position,
                        )
                        if direction is not None:
                            vanguard.sweep(direction)
                            _record_planned_cell_damage(
                                defender.position,
                                enemies,
                                planned_damage,
                            )
                            continue
                    breach_position = (
                        min(
                            raid_defenders,
                            key=lambda enemy: (
                                _distance(vanguard.position, enemy.position),
                                _combat_target_key(vanguard.position, enemy),
                            ),
                        ).position
                        if raid_defenders
                        else isolated_core_target.position
                    )
                    if not _queue_toward(
                        vanguard,
                        breach_position,
                        context,
                        avoid_danger=False,
                    ):
                        vanguard.wait()
                    continue
                direction = _direction_to_adjacent(
                    vanguard.position,
                    isolated_core_target.position,
                )
                if direction is not None and visible_target is not None:
                    vanguard.sweep(direction)
                elif not _queue_toward(
                    vanguard,
                    isolated_core_target.position,
                    context,
                ):
                    vanguard.wait()
                continue
            nearby_enemies = [
                enemy
                for enemy in avoidance_enemies
                if _distance(vanguard.position, enemy.position)
                <= UNIT_EVADE_TRIGGER_DISTANCE
            ]
            adjacent = [
                enemy
                for enemy in nearby_enemies
                if _distance(vanguard.position, enemy.position) == 1
            ]
            if self.combat_pressure_active and adjacent:
                target = min(
                    adjacent,
                    key=lambda enemy: _projected_combat_target_key(
                        vanguard.position,
                        enemy,
                        planned_damage,
                    ),
                )
                direction = _direction_to_adjacent(vanguard.position, target.position)
                if direction is not None:
                    vanguard.sweep(direction)
                    _record_planned_cell_damage(
                        target.position,
                        enemies,
                        planned_damage,
                    )
                    continue
            if self.combat_pressure_active:
                target_position = _guard_post(
                    vanguard,
                    core.position,
                    context,
                    _defense_post_directions(
                        core.position,
                        enemies,
                        CARDINAL_DIRECTIONS,
                        defender_index=index,
                        priority_ids=(
                            self.active_enemy_ids | self.pursuing_enemy_ids
                        ),
                    ),
                    VANGUARD_GUARD_RADIUS,
                )
                if target_position != vanguard.position and _queue_toward(
                    vanguard,
                    target_position,
                    context,
                ):
                    continue
                vanguard.wait()
                continue
            if _queue_away_from_enemies(
                vanguard,
                nearby_enemies,
                context,
                turn.beacon.position,
                keep_core_neighbors_clear=True,
            ):
                continue
            if adjacent:
                target = min(
                    adjacent,
                    key=lambda enemy: _projected_combat_target_key(
                        vanguard.position,
                        enemy,
                        planned_damage,
                    ),
                )
                direction = _direction_to_adjacent(vanguard.position, target.position)
                if direction is not None:
                    vanguard.sweep(direction)
                    _record_planned_cell_damage(
                        target.position,
                        enemies,
                        planned_damage,
                    )
                    continue

            if nearby_enemies:
                vanguard.wait()
                continue

            target_position = _guard_post(
                vanguard,
                core.position,
                context,
                _rotate_directions(
                    (
                        Direction.DOWN,
                        Direction.UP,
                        Direction.LEFT,
                        Direction.RIGHT,
                    ),
                    index,
                ),
                VANGUARD_GUARD_RADIUS,
            )
            if target_position != vanguard.position:
                moved = _queue_toward(
                    vanguard,
                    target_position,
                    context,
                )
                if moved:
                    continue
            vanguard.wait()

    def _control_rangers(
        self,
        turn: Turn,
        enemies: Sequence[object],
        context: MovementContext,
        isolated_core_target: object | None,
        planned_damage: dict[UUID, int],
    ) -> None:
        core = turn.core
        if core is None:
            return

        target_id = getattr(isolated_core_target, "id", None)
        visible_target = (
            isolated_core_target.visible_enemy
            if isinstance(isolated_core_target, CoreRaidTarget)
            else isolated_core_target
        )
        avoidance_enemies = tuple(
            enemy for enemy in enemies if enemy.id != target_id
        )
        core_threats = _core_threatening_enemies(
            core.position,
            enemies,
            context.obstacles,
        )
        _, strike_rangers = self._strike_group_ids(turn, isolated_core_target)
        ranger_current_targets: set[UUID] = set()
        predicted_enemy_ids: set[UUID] = set()
        for index, ranger in enumerate(
            sorted(turn.rangers, key=_uuid_sort_key)
        ):
            if context.preplanned_units and ranger.id in context.preplanned_units:
                continue
            immediate_core_threats = [
                enemy
                for enemy in core_threats
                if _distance(ranger.position, core.position)
                <= CORE_PROTECTOR_RADIUS
                and _ranger_can_shoot(
                    ranger.position,
                    enemy.position,
                    context.obstacles,
                )
            ]
            if immediate_core_threats:
                target = min(
                    immediate_core_threats,
                    key=lambda enemy: _projected_combat_target_key(
                        ranger.position,
                        enemy,
                        planned_damage,
                    ),
                )
                _queue_ranger_attack(ranger, target, turn.visible_enemies)
                _record_planned_target_damage(target, planned_damage)
                continue
            if self._healing_return_ready(turn, ranger):
                if ranger.position == core.position:
                    ranger.heal()
                elif not _queue_toward(
                    ranger,
                    core.position,
                    context,
                    allow_core_entry=True,
                    allow_single_friendly_transit=True,
                ):
                    ranger.wait()
                continue
            if self._control_returning_defender(turn, ranger, context):
                continue
            pursuing_targets = [
                enemy
                for enemy in enemies
                if enemy.id in self.pursuing_enemy_ids
                and _ranger_can_shoot(
                    ranger.position,
                    enemy.position,
                    context.obstacles,
                )
            ]
            if pursuing_targets:
                pursuer = min(
                    pursuing_targets,
                    key=lambda enemy: _projected_combat_target_key(
                        ranger.position,
                        enemy,
                        planned_damage,
                    ),
                )
                predicted_cell = None
                if (
                    pursuer.id in ranger_current_targets
                    and pursuer.id not in predicted_enemy_ids
                ):
                    predicted_cell = _predicted_motion_cell(
                        self.enemy_unit_motion.get(pursuer.id)
                    )
                if (
                    predicted_cell is not None
                    and predicted_cell not in context.obstacles
                    and _ranger_can_shoot(
                        ranger.position,
                        predicted_cell,
                        context.obstacles,
                    )
                ):
                    ranger.shoot_cell(predicted_cell)
                    predicted_enemy_ids.add(pursuer.id)
                    _record_planned_cell_damage(
                        predicted_cell,
                        turn.visible_enemies,
                        planned_damage,
                    )
                else:
                    _queue_ranger_attack(ranger, pursuer, turn.visible_enemies)
                    _record_planned_target_damage(pursuer, planned_damage)
                    ranger_current_targets.add(pursuer.id)
                continue
            strike_member = ranger.id in strike_rangers
            if strike_member:
                if isinstance(isolated_core_target, CoreRaidTarget):
                    local_opponents = self._raid_local_opponents(turn)
                    shootable_opponents = [
                        enemy
                        for enemy in local_opponents
                        if _ranger_can_shoot(
                            ranger.position,
                            enemy.position,
                            context.obstacles,
                        )
                    ]
                    if shootable_opponents:
                        opponent = min(
                            shootable_opponents,
                            key=lambda enemy: _projected_combat_target_key(
                                ranger.position,
                                enemy,
                                planned_damage,
                            ),
                        )
                        _queue_ranger_attack(
                            ranger,
                            opponent,
                            turn.visible_enemies,
                        )
                        _record_planned_target_damage(opponent, planned_damage)
                        continue
                if (
                    isinstance(isolated_core_target, CoreRaidTarget)
                    and self.raid_phase is RaidPhase.STAGE
                ):
                    stage_position = self.raid_stage_assignments.get(
                        ranger.id,
                        isolated_core_target.position,
                    )
                    if (
                        _distance(ranger.position, stage_position)
                        <= CORE_RAID_STAGE_TOLERANCE
                    ):
                        ranger.wait()
                    elif not _queue_toward(
                        ranger,
                        stage_position,
                        context,
                    ):
                        ranger.wait()
                    continue
                if (
                    isinstance(isolated_core_target, CoreRaidTarget)
                    and self.raid_phase is RaidPhase.BREACH
                ):
                    raid_opponents = self._raid_breach_opponents(
                        turn,
                        isolated_core_target.position,
                    )
                    shootable_opponents = [
                        enemy
                        for enemy in raid_opponents
                        if _ranger_can_shoot(
                            ranger.position,
                            enemy.position,
                            context.obstacles,
                        )
                    ]
                    if shootable_opponents:
                        opponent = min(
                            shootable_opponents,
                            key=lambda enemy: _projected_combat_target_key(
                                ranger.position,
                                enemy,
                                planned_damage,
                            ),
                        )
                        _queue_ranger_attack(
                            ranger,
                            opponent,
                            turn.visible_enemies,
                        )
                        _record_planned_target_damage(opponent, planned_damage)
                        continue
                    if not raid_opponents and _ranger_can_shoot(
                        ranger.position,
                        isolated_core_target.position,
                        context.obstacles,
                    ):
                        ranger.wait()
                        continue
                    breach_position = (
                        min(
                            raid_opponents,
                            key=lambda enemy: (
                                _distance(ranger.position, enemy.position),
                                _combat_target_key(ranger.position, enemy),
                            ),
                        ).position
                        if raid_opponents
                        else isolated_core_target.position
                    )
                    if not _queue_toward(
                        ranger,
                        breach_position,
                        context,
                        avoid_danger=False,
                    ):
                        ranger.wait()
                    continue
                can_shoot_target_cell = _ranger_can_shoot(
                    ranger.position,
                    isolated_core_target.position,
                    context.obstacles,
                )
                if visible_target is not None and can_shoot_target_cell:
                    ranger.shoot(visible_target)
                elif (
                    isinstance(isolated_core_target, CoreRaidTarget)
                    and can_shoot_target_cell
                ):
                    ranger.shoot_cell(isolated_core_target.position)
                elif not _queue_toward(
                    ranger,
                    isolated_core_target.position,
                    context,
                ):
                    ranger.wait()
                continue
            nearby_enemies = [
                enemy
                for enemy in avoidance_enemies
                if _distance(ranger.position, enemy.position)
                <= UNIT_EVADE_TRIGGER_DISTANCE
            ]
            shootable = [
                enemy
                for enemy in nearby_enemies
                if _ranger_can_shoot(
                    ranger.position,
                    enemy.position,
                    context.obstacles,
                )
            ]
            if self.combat_pressure_active and shootable:
                target = min(
                    shootable,
                    key=lambda enemy: _projected_combat_target_key(
                        ranger.position,
                        enemy,
                        planned_damage,
                    ),
                )
                _queue_ranger_attack(ranger, target, turn.visible_enemies)
                _record_planned_target_damage(target, planned_damage)
                continue
            if self.combat_pressure_active:
                target_position = _guard_post(
                    ranger,
                    core.position,
                    context,
                    _defense_post_directions(
                        core.position,
                        enemies,
                        CARDINAL_DIRECTIONS,
                        defender_index=index,
                        priority_ids=(
                            self.active_enemy_ids | self.pursuing_enemy_ids
                        ),
                    ),
                    RANGER_GUARD_RADIUS,
                )
                if target_position != ranger.position and _queue_toward(
                    ranger,
                    target_position,
                    context,
                ):
                    continue
                ranger.wait()
                continue
            if _queue_away_from_enemies(
                ranger,
                nearby_enemies,
                context,
                turn.beacon.position,
                keep_core_neighbors_clear=True,
            ):
                continue
            if shootable:
                target = min(
                    shootable,
                    key=lambda enemy: _projected_combat_target_key(
                        ranger.position,
                        enemy,
                        planned_damage,
                    ),
                )
                _queue_ranger_attack(ranger, target, turn.visible_enemies)
                _record_planned_target_damage(target, planned_damage)
                continue

            if nearby_enemies:
                ranger.wait()
                continue

            target_position = _guard_post(
                ranger,
                core.position,
                context,
                _rotate_directions(
                    (
                        Direction.LEFT,
                        Direction.RIGHT,
                        Direction.UP,
                        Direction.DOWN,
                    ),
                    index,
                ),
                RANGER_GUARD_RADIUS,
            )
            if target_position != ranger.position:
                moved = _queue_toward(
                    ranger,
                    target_position,
                    context,
                )
                if moved:
                    continue
            ranger.wait()

    def _should_wait_for_cargo(
        self,
        turn: Turn,
        context: MovementContext,
    ) -> bool:
        core = turn.core
        if core is None or turn.resource_space <= 0:
            return False
        cargo_workers = [worker for worker in turn.workers if worker.cargo > 0]
        if not cargo_workers:
            return False

        blocked = (
            set(context.obstacles)
            | set(context.enemy_cells)
            | set(context.danger_cells)
        )
        return_etas = [
            _estimated_path_cost(worker.position, core.position, blocked)
            for worker in cargo_workers
        ]
        nearest_eta = min(return_etas)
        total_cargo = sum(worker.cargo for worker in cargo_workers)
        return (
            total_cargo >= CORE_CONGESTED_CARGO
            or nearest_eta <= CORE_SHORT_CARGO_ETA
            or (
                total_cargo >= CORE_BULK_CARGO
                and nearest_eta <= CORE_BULK_CARGO_ETA
            )
        )

    def _core_blocked_cells(
        self,
        turn: Turn,
        context: MovementContext,
    ) -> set[Position]:
        blocked = (
            set(context.obstacles)
            | set(context.enemy_cells)
            | set(turn.resource_cells)
        )
        blocked.update(
            cell
            for cell, occupants in context.friendly_counts.items()
            if occupants >= 2 and cell != context.core_position
        )
        return blocked

    def _start_core_retreat(
        self,
        turn: Turn,
        context: MovementContext,
        enemies: Sequence[object],
        *,
        reason: str,
    ) -> bool:
        core = turn.core
        if core is None:
            return False
        direction = _retreat_direction(
            core.position,
            turn.beacon.position,
            enemies,
            context.obstacles,
            self._core_blocked_cells(turn, context),
            self.last_retreat_direction,
            allow_beacon_approach=reason == "EVADE",
        )
        if direction is None:
            return False
        core.start_move(direction)
        self.last_retreat_direction = direction
        self.active_core_move_reason = reason
        return True

    def _moving_core_should_cancel(
        self,
        turn: Turn,
        context: MovementContext,
        enemies: Sequence[object],
        *,
        projected_core_damage: int,
        core_survival_margin: int,
    ) -> bool:
        core = turn.core
        if core is None or core.view.destination is None:
            return False

        self.last_core_cancel_reason = "NONE"
        destination = core.view.destination
        if destination in self._core_blocked_cells(turn, context):
            self.last_core_cancel_reason = "DESTINATION_BLOCKED"
            return True

        if enemies:
            current_threat_key = _position_threat_key(
                core.position,
                enemies,
                context.obstacles,
            )
            destination_threat_key = _position_threat_key(
                destination,
                enemies,
                context.obstacles,
            )
            current_enemy_distance = _minimum_enemy_distance(core.position, enemies)
            destination_enemy_distance = _minimum_enemy_distance(destination, enemies)
            enemy_cancel_radius = (
                CORE_EVADE_RELEASE_DISTANCE
                if self.active_core_move_reason == "EVADE"
                else CORE_EVADE_TRIGGER_DISTANCE
            )
            enemy_threat_relevant = (
                min(current_enemy_distance, destination_enemy_distance)
                <= enemy_cancel_radius
            )
            if (
                enemy_threat_relevant
                and destination_threat_key[0] > current_threat_key[0]
            ):
                self.last_core_cancel_reason = "PROJECTED_DAMAGE_WORSE"
                return True
            if (
                self.active_core_move_reason == "EVADE"
                and self.combat_pressure_active
                and destination_threat_key[0] <= current_threat_key[0]
            ):
                return False
            if enemy_threat_relevant and destination_threat_key > current_threat_key:
                self.last_core_cancel_reason = "ENEMY_RISK_WORSE"
                return True
            if destination_threat_key <= current_threat_key:
                return False

        projected_hp_damage = max(0, projected_core_damage - core.shield)
        if (
            projected_hp_damage > 0
            and core_survival_margin > 0
            and turn.resources >= 1
        ):
            self.last_core_cancel_reason = "PROJECTED_HEAL"
            return True

        if (
            self.active_core_move_reason == "EVADE"
            and turn.tick <= self.threat_caution_until_tick
        ):
            return False

        move_progress = core.view.move_progress or 0
        move_committed = move_progress >= CORE_MOVE_COMMIT_PROGRESS
        cargo_on_core = any(
            worker.cargo > 0 and worker.position == core.position
            for worker in turn.workers
        )
        if cargo_on_core or (
            not move_committed and self._should_wait_for_cargo(turn, context)
        ):
            self.last_core_cancel_reason = "CARGO_DELIVERY"
            return True

        cancel_for_beacon = (
            not move_committed
            and self.active_core_move_reason != "EVADE"
            and self.beacon_policy == "retreat"
            and _distance(destination, turn.beacon.position)
            < _distance(core.position, turn.beacon.position)
        )
        if cancel_for_beacon:
            self.last_core_cancel_reason = "BEACON_APPROACH"
        return cancel_for_beacon

    def _control_core(
        self,
        turn: Turn,
        context: MovementContext,
        isolated_core_target: object | None,
    ) -> None:
        core = turn.core
        if core is None:
            return
        enemies = tuple(
            enemy
            for enemy in turn.visible_enemies
            if getattr(enemy, "kind") != "CORE"
            and enemy.unit_type in {UnitType.VANGUARD, UnitType.RANGER}
        )
        retreat_enemies = enemies + self._remembered_retreat_threats(turn, enemies)
        projected_core_damage = _projected_core_damage(
            core.position,
            enemies,
            context.obstacles,
        )
        projected_hp_damage = max(0, projected_core_damage - core.shield)
        core_survival_margin = core.hp - projected_hp_damage
        self.last_projected_core_damage = projected_core_damage
        self.last_core_survival_margin = core_survival_margin
        if _is_multi_axis_breakout(
            core.position,
            enemies,
            context.obstacles,
            self._core_blocked_cells(turn, context),
        ):
            self._refresh_threat_assessment(turn, breakout=True)
        if core.view.state is CoreState.MOVING:
            if (
                self.compatibility_hold
                and self.active_core_move_reason != "EVADE"
            ):
                core.cancel_move()
                self.last_core_cancel_reason = "COMPATIBILITY_HOLD"
                self.last_core_move_tick = turn.tick
                self.last_retreat_direction = None
                self.active_core_move_reason = None
                return
            if self._moving_core_should_cancel(
                turn,
                context,
                retreat_enemies,
                projected_core_damage=projected_core_damage,
                core_survival_margin=core_survival_margin,
            ):
                core.cancel_move()
                self.last_core_move_tick = turn.tick
                self.last_retreat_direction = None
                self.active_core_move_reason = None
            return
        if core.view.state is not CoreState.NORMAL:
            return

        if (
            not self.compatibility_hold
            and
            self.beacon_policy == "pursue"
            and core.position == turn.beacon.position
            and turn.beacon.status is BeaconStatus.GROUND
        ):
            core.pickup_beacon()
            return

        population = len(turn.units)
        worker_cost = unit_cost(UnitType.WORKER, population)
        vanguard_cost = unit_cost(UnitType.VANGUARD, population)
        ranger_cost = unit_cost(UnitType.RANGER, population)
        available_resources = _projected_core_resources(turn)
        can_spawn = (
            not self.compatibility_hold
            and
            context.friendly_counts[core.position] < 2
            and population < PLANNED_POPULATION_CAP
        )
        nearest_threat = min(
            (
                _distance(core.position, enemy.position)
                for enemy in retreat_enemies
            ),
            default=None,
        )
        critical_core = core.shield == 0 and core.hp <= 2
        projected_nonfatal_hp_damage = (
            projected_hp_damage > 0 and core_survival_margin > 0
        )
        cargo_waiting = self._should_wait_for_cargo(turn, context)
        if (
            retreat_enemies
            and nearest_threat is not None
            and (
                nearest_threat <= CORE_EVADE_TRIGGER_DISTANCE
                or self.preemptive_evade_enemy_ids
                or self.pursuing_enemy_ids
                or turn.tick <= self.recent_core_attack_until_tick
            )
            and self._start_core_retreat(
                turn,
                context,
                retreat_enemies,
                reason="EVADE",
            )
        ):
            return

        if (
            available_resources >= 1
            and core_survival_margin > 0
            and (
                (critical_core and core.hp < 5)
                or projected_nonfatal_hp_damage
            )
        ):
            core.heal()
            return

        if core.hp < 5 and available_resources >= 1 and core_survival_margin > 0:
            core.heal()
            return

        if core.shield < 5 and available_resources >= 1:
            core.repair_shield()
            return

        if self.compatibility_hold:
            core.wait()
            return

        if (
            not enemies
            and not self.recovery_mode
            and turn.tick <= self.threat_caution_until_tick
        ):
            core.wait()
            return

        # Production is a last resort when a fully shielded Core cannot open a
        # safe escape route. Newly spawned Units cannot act in their creation Tick.
        if can_spawn:
            if (
                nearest_threat is not None
                and nearest_threat <= 3
                and len(turn.vanguards) < DEFENSE_VANGUARD_TARGET
                and available_resources >= vanguard_cost
            ):
                core.spawn(UnitType.VANGUARD)
                return
            if (
                nearest_threat is not None
                and nearest_threat <= 6
                and len(turn.workers) >= 4
                and len(turn.rangers) < DEFENSE_RANGER_TARGET
                and available_resources >= ranger_cost
            ):
                core.spawn(UnitType.RANGER)
                return

        missing_vanguards, missing_rangers = self._raid_rebuild_missing(turn)
        rebuild_is_safe = nearest_threat is None and not self.combat_pressure_active
        recovery_worker_floor = min(RECOVERY_MIN_WORKERS, self.worker_target)
        if (
            rebuild_is_safe
            and self.recovery_mode
            and (missing_vanguards or missing_rangers)
            and len(turn.workers) < recovery_worker_floor
        ):
            if can_spawn and available_resources >= worker_cost:
                core.spawn(UnitType.WORKER)
            else:
                core.wait()
            return
        if rebuild_is_safe and (missing_vanguards or missing_rangers):
            if (
                can_spawn
                and missing_vanguards
                and available_resources >= vanguard_cost
            ):
                core.spawn(UnitType.VANGUARD)
            elif (
                can_spawn
                and missing_rangers
                and available_resources >= ranger_cost
            ):
                core.spawn(UnitType.RANGER)
            else:
                core.wait()
            return

        if isolated_core_target is not None:
            core.wait()
            return

        if self.combat_pressure_active:
            core.wait()
            return

        if can_spawn:
            economic_expansion_is_safe = (
                nearest_threat is None or nearest_threat > 6
            )
            if self.recovery_mode and economic_expansion_is_safe:
                vanguard_worker_goal = min(
                    RECOVERY_VANGUARD_WORKER_GOAL,
                    self.worker_target,
                )
                ranger_worker_goal = min(
                    RECOVERY_RANGER_WORKER_GOAL,
                    self.worker_target,
                )
                if len(turn.workers) < vanguard_worker_goal:
                    if available_resources >= worker_cost:
                        core.spawn(UnitType.WORKER)
                    else:
                        core.wait()
                    return
                if len(turn.vanguards) < EARLY_DEFENSE_VANGUARD_TARGET:
                    if available_resources >= vanguard_cost:
                        core.spawn(UnitType.VANGUARD)
                    else:
                        core.wait()
                    return
                if len(turn.workers) < ranger_worker_goal:
                    if available_resources >= worker_cost:
                        core.spawn(UnitType.WORKER)
                    else:
                        core.wait()
                    return
                if len(turn.rangers) < EARLY_DEFENSE_RANGER_TARGET:
                    if available_resources >= ranger_cost:
                        core.spawn(UnitType.RANGER)
                    else:
                        core.wait()
                    return

            early_worker_goal = min(
                EARLY_DEFENSE_WORKER_GOAL,
                self.worker_target,
            )
            early_defense_is_safe = (
                len(turn.workers) >= early_worker_goal
                and nearest_threat is None
            )
            if (
                early_defense_is_safe
                and len(turn.vanguards) < EARLY_DEFENSE_VANGUARD_TARGET
                and available_resources
                >= EARLY_DEFENSE_RESERVE + vanguard_cost
            ):
                core.spawn(UnitType.VANGUARD)
                return
            if (
                early_defense_is_safe
                and len(turn.vanguards) >= EARLY_DEFENSE_VANGUARD_TARGET
                and len(turn.rangers) < EARLY_DEFENSE_RANGER_TARGET
                and available_resources >= EARLY_DEFENSE_RESERVE + ranger_cost
            ):
                core.spawn(UnitType.RANGER)
                return

            # Once the worker economy reaches its middle milestone, pause
            # worker growth until a 4V/4R screen exists. This keeps the Core
            # from spending a long vulnerable stretch with only the 1V/1R
            # emergency pair while still allowing the 18-worker end state.
            mid_worker_goal = min(MIDGAME_WORKER_GOAL, self.worker_target)
            mid_vanguard_goal = min(MIDGAME_VANGUARD_TARGET, DEFENSE_VANGUARD_TARGET)
            mid_ranger_goal = min(MIDGAME_RANGER_TARGET, DEFENSE_RANGER_TARGET)
            mid_force_complete = (
                len(turn.workers) < mid_worker_goal
                or (
                    len(turn.vanguards) >= mid_vanguard_goal
                    and len(turn.rangers) >= mid_ranger_goal
                )
            )
            if (
                len(turn.workers) >= mid_worker_goal
                and len(turn.vanguards) < mid_vanguard_goal
                and available_resources >= EARLY_DEFENSE_RESERVE + vanguard_cost
                and economic_expansion_is_safe
            ):
                core.spawn(UnitType.VANGUARD)
                return
            if (
                len(turn.workers) >= mid_worker_goal
                and len(turn.vanguards) >= mid_vanguard_goal
                and len(turn.rangers) < mid_ranger_goal
                and available_resources >= EARLY_DEFENSE_RESERVE + ranger_cost
                and economic_expansion_is_safe
            ):
                core.spawn(UnitType.RANGER)
                return

            if (
                self.recovery_mode
                and len(turn.workers)
                < min(RECOVERY_MIN_WORKERS, self.worker_target)
            ):
                expansion_threshold = worker_cost
            else:
                expansion_threshold = _worker_expansion_threshold(
                    len(turn.workers),
                    self.worker_target,
                    turn.resource_capacity,
                    population,
                )
            if (
                len(turn.workers) < self.worker_target
                and mid_force_complete
                and available_resources >= expansion_threshold
                and economic_expansion_is_safe
            ):
                core.spawn(UnitType.WORKER)
                return

            mature_for_defense = (
                len(turn.workers) >= self.worker_target
                and nearest_threat is None
                and available_resources >= LONG_TERM_DEFENSE_RESERVE
            )
            if mature_for_defense and len(turn.vanguards) < DEFENSE_VANGUARD_TARGET:
                if available_resources >= LONG_TERM_DEFENSE_RESERVE + vanguard_cost:
                    core.spawn(UnitType.VANGUARD)
                    return
            if (
                mature_for_defense
                and len(turn.vanguards) >= DEFENSE_VANGUARD_TARGET
                and len(turn.rangers) < DEFENSE_RANGER_TARGET
            ):
                if available_resources >= LONG_TERM_DEFENSE_RESERVE + ranger_cost:
                    core.spawn(UnitType.RANGER)
                    return

        if cargo_waiting:
            core.wait()
            return

        if self.recovery_mode:
            # Rebuild locally instead of advertising the Core on the public
            # Beacon route.
            core.wait()
            return

        if self.beacon_policy == "hold":
            core.wait()
            return

        if self.beacon_policy == "retreat":
            early_worker_goal = min(
                EARLY_DEFENSE_WORKER_GOAL,
                self.worker_target,
            )
            early_fleet_ready = (
                len(turn.workers) >= early_worker_goal
                and len(turn.vanguards) >= EARLY_DEFENSE_VANGUARD_TARGET
                and len(turn.rangers) >= EARLY_DEFENSE_RANGER_TARGET
            )
            service_window_complete = (
                turn.tick
                - max(
                    self.last_core_move_tick,
                    self.startup_tick
                    if self.startup_tick is not None
                    else self.last_core_move_tick,
                )
                >= RETREAT_SERVICE_TICKS
            )
            needs_more_beacon_distance = (
                _distance(core.position, turn.beacon.position)
                < RETREAT_MIN_BEACON_DISTANCE
            )
            if (
                early_fleet_ready
                and service_window_complete
                and needs_more_beacon_distance
                and self._start_core_retreat(
                    turn,
                    context,
                    enemies,
                    reason="RETREAT",
                )
            ):
                return
            core.wait()
            return

        if core.position == turn.beacon.position:
            return

        directions = _path_directions(
            core.position,
            turn.beacon.position,
            self._core_blocked_cells(turn, context),
        )
        if directions:
            core.start_move(directions[0])


def _event_int(event: object, name: str) -> int:
    values = getattr(event, "values", None)
    if not isinstance(values, Mapping):
        return 0
    value = values.get(name)
    return value if isinstance(value, int) and not isinstance(value, bool) and value >= 0 else 0


def _resource_event_effect(event: object) -> int:
    event_type = getattr(event, "event_type", "")
    if event_type in {"DEPOSIT_SUCCEEDED", "CORE_RESOURCES_CAPTURED"}:
        return _event_int(event, "amount")
    if event_type == "CORE_RESOURCE_OVERFLOW_DESTROYED":
        return -_event_int(event, "amount")
    if event_type in {
        "UNIT_HEAL_SUCCEEDED",
        "CORE_HEAL_SUCCEEDED",
        "CORE_REPAIR_SUCCEEDED",
        "CORE_SPAWN_SUCCEEDED",
    }:
        return -_event_int(event, "cost")
    return 0


def _resource_ledger_snapshot(turn: Turn) -> ResourceLedgerSnapshot:
    plan = turn.plan.model_dump(mode="json", exclude_none=True)
    core_action = plan.get("core_action", {})
    core_action_name = core_action.get("type", "NONE")
    if direction := core_action.get("direction"):
        core_action_name = f"{core_action_name}:{direction}"
    actions, _ = _turn_diagnostics(turn)
    return ResourceLedgerSnapshot(
        tick=turn.tick,
        resources=turn.resources,
        population=len(turn.units),
        workers=len(turn.workers),
        vanguards=len(turn.vanguards),
        rangers=len(turn.rangers),
        actions=actions,
        core_action=core_action_name,
    )


def _reconcile_resource_turn(
    previous: ResourceLedgerSnapshot,
    turn: Turn,
) -> ResourceLedgerResult:
    actual_delta = turn.resources - previous.resources
    _, events = _turn_diagnostics(turn)
    skipped_reason = None
    if turn.tick != previous.tick + 1:
        skipped_reason = "tick_gap"
    elif any(
        event.event_type in {"CORE_DESTROYED", "CORE_RESPAWNED"}
        for event in turn.events
    ):
        skipped_reason = "core_lifecycle"

    expected_delta = (
        actual_delta
        if skipped_reason is not None
        else sum(_resource_event_effect(event) for event in turn.events)
    )
    return ResourceLedgerResult(
        previous=previous,
        tick=turn.tick,
        resources=turn.resources,
        population=len(turn.units),
        workers=len(turn.workers),
        vanguards=len(turn.vanguards),
        rangers=len(turn.rangers),
        actual_delta=actual_delta,
        expected_delta=expected_delta,
        unexplained_delta=actual_delta - expected_delta,
        events=events,
        skipped_reason=skipped_reason,
    )


def _emit_resource_ledger(result: ResourceLedgerResult) -> None:
    if result.actual_delta >= 0 and result.unexplained_loss == 0:
        return
    previous = result.previous
    prefix = (
        "WARNING unexplained_resource_loss"
        if result.unexplained_loss
        else "RESOURCE_LEDGER"
    )
    print(
        f"{prefix} tick={result.tick} previous_tick={previous.tick} "
        f"resources={previous.resources}->{result.resources} "
        f"actual_delta={result.actual_delta} expected_delta={result.expected_delta} "
        f"unexplained_delta={result.unexplained_delta} "
        f"unexplained_loss={result.unexplained_loss} "
        f"previous_population={previous.population} current_population={result.population} "
        f"previous_fleet={previous.workers}W:{previous.vanguards}V:{previous.rangers}R "
        f"current_fleet={result.workers}W:{result.vanguards}V:{result.rangers}R "
        f"previous_actions={previous.actions} previous_core_action={previous.core_action} "
        f"events={result.events} skipped_reason={result.skipped_reason or 'none'}",
        file=sys.stderr if result.unexplained_loss else sys.stdout,
        flush=True,
    )


def _format_counts(counts: Counter[str]) -> str:
    if not counts:
        return "none"
    return ",".join(f"{name}:{counts[name]}" for name in sorted(counts))


def _visible_enemy_counts(turn: Turn) -> Counter[str]:
    counts: Counter[str] = Counter()
    for enemy in turn.visible_enemies:
        if getattr(enemy, "kind") == "CORE":
            counts["CORE"] += 1
        else:
            counts[getattr(enemy, "unit_type").value] += 1
    return counts


def _turn_diagnostics(turn: Turn) -> tuple[str, str]:
    plan = turn.plan.model_dump(mode="json", exclude_none=True)
    action_counts = Counter(
        action["type"] for action in plan.get("unit_actions", {}).values()
    )
    core_action = plan.get("core_action")
    if core_action:
        action_counts[core_action["type"]] += 1
    event_counts = Counter(
        (
            f"{event.event_type}/{event.reason_code}"
            if event.reason_code
            else event.event_type
        )
        for event in turn.events
    )
    return _format_counts(action_counts), _format_counts(event_counts)


def _position_diagnostics(turn: Turn, tactic: CoreFarmer) -> str:
    core = turn.core
    if core is None:
        return "core=respawning"
    plan = turn.plan.model_dump(mode="json", exclude_none=True)
    unit_actions = plan.get("unit_actions", {})
    worker_parts = []
    for worker in sorted(turn.workers, key=_uuid_sort_key):
        action = unit_actions.get(str(worker.id), {})
        action_name = action.get("type", "NONE")
        if direction := action.get("direction"):
            action_name = f"{action_name}:{direction}"
        mode = tactic.worker_modes.get(worker.id, "UNKNOWN")
        target = tactic.worker_targets.get(worker.id)
        target_text = (
            f"/t{target[0]}:{target[1]}" if target is not None else ""
        )
        worker_parts.append(
            f"{str(worker.id)[:6]}@{worker.position[0]}:{worker.position[1]}"
            f"/c{worker.cargo}/a{action_name}/m{mode}{target_text}"
        )
    workers = ";".join(worker_parts)
    defender_parts = []
    for defender in sorted((*turn.vanguards, *turn.rangers), key=_uuid_sort_key):
        action = unit_actions.get(str(defender.id), {})
        action_name = action.get("type", "NONE")
        if direction := action.get("direction"):
            action_name = f"{action_name}:{direction}"
        defender_parts.append(
            f"{defender.unit_type.value[0]}{str(defender.id)[:6]}@"
            f"{defender.position[0]}:{defender.position[1]}/a{action_name}"
        )
    defenders = ";".join(defender_parts)
    defender_on_core = sum(
        defender.position == core.position
        for defender in (*turn.vanguards, *turn.rangers)
    )
    delivery_blocked = sum(
        mode in {"RETURN_BLOCKED", "CLEAR_CORE_BLOCKED"}
        for mode in tactic.worker_modes.values()
    )
    resource_blocked = sum(
        mode == "RESOURCE_BLOCKED" for mode in tactic.worker_modes.values()
    )
    scout_oldest_age = max(
        (
            turn.tick - last_seen
            for last_seen in tactic.scout_chunk_last_seen.values()
        ),
        default=0,
    )
    captured_resources = sum(
        capture.amount
        for event in turn.events
        if (capture := event.core_resource_capture) is not None
    )
    capture_destroyed = sum(
        capture.destroyed
        for event in turn.events
        if (capture := event.core_resource_capture) is not None
    )
    core_healed = sum(
        healing.amount
        for event in turn.events
        if event.event_type == "CORE_HEAL_SUCCEEDED"
        and (healing := event.healing) is not None
    )
    unit_healed = sum(
        healing.amount
        for event in turn.events
        if event.event_type == "UNIT_HEAL_SUCCEEDED"
        and (healing := event.healing) is not None
    )
    spawn_cost = sum(
        _event_int(event, "cost")
        for event in turn.events
        if event.event_type == "CORE_SPAWN_SUCCEEDED"
    )
    spawn_required = max(
        (
            _event_int(event, "required")
            for event in turn.events
            if event.event_type == "CORE_SPAWN_FAILED"
            and event.reason_code == "INSUFFICIENT_RESOURCES"
        ),
        default=0,
    )
    population = len(turn.units)
    raid_missing_vanguards, raid_missing_rangers = (
        tactic._raid_rebuild_missing(turn)
    )
    enemy_counts = _visible_enemy_counts(turn)
    core_action = plan.get("core_action", {})
    core_action_name = core_action.get("type", "NONE")
    if direction := core_action.get("direction"):
        core_action_name = f"{core_action_name}:{direction}"
    beacon_distance = _distance(core.position, turn.beacon.position)
    movement = ""
    if core.view.state is CoreState.MOVING:
        movement = (
            f"/p{core.view.move_progress}:{core.view.move_required_ticks}"
            f"->{core.view.destination[0]}:{core.view.destination[1]}"
        )
    episode = tactic.active_raid_episode
    if episode is None:
        raid_episode_state = "IDLE"
        raid_episode_target = "none"
        raid_episode_outcome = "NONE"
        raid_episode_started = 0
        raid_episode_elapsed = 0
        raid_episode_pending_return = 0
        raid_episode_pending_scout = 0
        raid_episode_pending_rebuild = "0V:0R"
    else:
        raid_episode_state = episode.state
        raid_episode_target = str(episode.target_id)[:8]
        raid_episode_outcome = episode.outcome
        raid_episode_started = episode.start_tick
        raid_episode_elapsed = turn.tick - episode.start_tick
        raid_episode_pending_return = len(
            episode.return_member_ids & tactic.squad_return_ids
        )
        raid_episode_pending_scout = len(
            episode.return_spotter_ids & tactic.scout_return_ids
        )
        raid_episode_pending_rebuild = (
            f"{max(0, episode.rebuild_vanguard_target - len(turn.vanguards))}V:"
            f"{max(0, episode.rebuild_ranger_target - len(turn.rangers))}R"
        )
    last_episode = tactic.raid_episode_history[-1] if tactic.raid_episode_history else None
    last_episode_summary = "none"
    if last_episode is not None:
        last_episode_summary = (
            f"{last_episode.outcome}/{last_episode.cycle_end_reason}"
            f"/t{last_episode.start_tick}-{last_episode.ready_tick}"
            f"/e{last_episode.engagement_duration}"
            f"/r{last_episode.recovery_duration}"
            f"/loss{last_episode.loss_count}"
            f"/res{last_episode.start_resources}>{last_episode.engagement_end_resources}"
            f">{last_episode.ready_resources}"
        )
    return (
        f"core={core.position[0]}:{core.position[1]} "
        f"core_state={core.view.state.value}{movement} "
        f"core_action={core_action_name} "
        f"beacon={turn.beacon.position[0]}:{turn.beacon.position[1]} "
        f"beacon_distance={beacon_distance} "
        f"known_resources={len(tactic.resource_last_seen)} "
        f"released_targets={len(tactic.last_released_targets)} "
        f"danger_cells={len(tactic.last_danger_cells)} "
        f"projected_core_damage={tactic.last_projected_core_damage} "
        f"core_survival_margin={tactic.last_core_survival_margin} "
        f"defender_on_core={defender_on_core} "
        f"delivery_blocked={delivery_blocked} "
        f"resource_blocked={resource_blocked} "
        f"scout_chunks={len(tactic.scout_chunk_last_seen)} "
        f"scout_oldest_age={scout_oldest_age} "
        f"captured_resources={captured_resources} "
        f"capture_destroyed={capture_destroyed} "
        f"core_healed={core_healed} "
        f"unit_healed={unit_healed} "
        f"spawn_cost={spawn_cost} "
        f"spawn_required={spawn_required} "
        f"next_worker_cost={unit_cost(UnitType.WORKER, population)} "
        f"next_vanguard_cost={unit_cost(UnitType.VANGUARD, population)} "
        f"next_ranger_cost={unit_cost(UnitType.RANGER, population)} "
        f"visible_enemies={len(turn.visible_enemies)} "
        f"enemy_types={_format_counts(enemy_counts)} "
        f"global_posture={tactic.threat_assessment.global_posture.value} "
        f"threat_level={tactic.threat_assessment.level.value} "
        f"threat_reason={tactic.threat_assessment.primary_reason} "
        f"stationary_core_memory={len(tactic.stationary_core_memory)} "
        f"clear_core_target={str(tactic.isolated_core_target_id)[:8] if tactic.isolated_core_target_id else 'none'} "
        f"core_spotter={str(tactic.core_raid_spotter_id)[:8] if tactic.core_raid_spotter_id else 'none'} "
        f"raid_mode={tactic.raid_mode.value if tactic.raid_mode else 'none'} "
        f"raid_phase={tactic.raid_phase.value if tactic.raid_phase else 'none'} "
        f"raid_group={len(tactic.raid_vanguard_ids)}V:{len(tactic.raid_ranger_ids)}R "
        f"raid_initial_defenders={len(tactic.raid_initial_defender_ids)} "
        f"raid_reserved_resources={tactic.raid_reserved_resources} "
        f"raid_rebuild={tactic.raid_rebuild_vanguard_target}V:{tactic.raid_rebuild_ranger_target}R "
        f"raid_missing={raid_missing_vanguards}V:{raid_missing_rangers}R "
        f"raid_abort_reason={tactic.raid_abort_reason} "
        f"raid_target_cooldowns={len(tactic.raid_target_cooldown_until)} "
        f"raid_episode_state={raid_episode_state} "
        f"raid_episode_target={raid_episode_target} "
        f"raid_episode_outcome={raid_episode_outcome} "
        f"raid_episode_started={raid_episode_started} "
        f"raid_episode_elapsed={raid_episode_elapsed} "
        f"raid_episode_pending_return={raid_episode_pending_return} "
        f"raid_episode_pending_scout={raid_episode_pending_scout} "
        f"raid_episode_pending_rebuild={raid_episode_pending_rebuild} "
        f"raid_episode_history={len(tactic.raid_episode_history)} "
        f"raid_episode_last={last_episode_summary} "
        f"clear_unit_target={str(tactic.stationary_unit_target_id)[:8] if tactic.stationary_unit_target_id else 'none'} "
        f"active_enemies={len(tactic.active_enemy_ids)} "
        f"preemptive_evade={len(tactic.preemptive_evade_enemy_ids)} "
        f"pursuing_enemies={len(tactic.pursuing_enemy_ids)} "
        f"recent_attack_threats={len(tactic.recent_attack_threats)} "
        f"recent_attack_until={tactic.recent_attack_until_tick} "
        f"recent_core_attack_until={tactic.recent_core_attack_until_tick} "
        f"combat_pressure={int(tactic.combat_pressure_active)} "
        f"squad_return={len(tactic.squad_return_ids)} "
        f"scout_return={len(tactic.scout_return_ids)} "
        f"squad_disengage_until={tactic.squad_disengage_until_tick} "
        f"healing_defenders={len(tactic.healing_defender_ids)} "
        f"compatibility_hold={int(tactic.compatibility_hold)} "
        f"threat_caution_until={tactic.threat_caution_until_tick} "
        f"core_cancel_reason={tactic.last_core_cancel_reason} "
        f"recovery_reason={tactic.recovery_reason} "
        f"recovery_until={tactic.recovery_until_tick} "
        f"defender_state={defenders or 'none'} "
        f"worker_state={workers or 'none'}"
    )


def _manual_override_summary(receipt: Received) -> str | None:
    if receipt.source is not CommandSource.MANUAL:
        return None
    unit_actions = len(receipt.plan.unit_actions)
    core_actions = int(receipt.plan.core_action is not None)
    return (
        f"WARNING tick={receipt.tick} manual_override "
        f"unit_actions={unit_actions} core_actions={core_actions}"
    )


def _is_turn_scoped_api_error(error_code: str) -> bool:
    return error_code in TURN_SKIP_API_ERRORS


def _notify_systemd(*lines: str) -> bool:
    address = os.environ.get("NOTIFY_SOCKET")
    if not address:
        return False
    if address.startswith("@"):
        address = "\0" + address[1:]
    payload = "\n".join(lines).encode("utf-8")
    try:
        with socket.socket(socket.AF_UNIX, socket.SOCK_DGRAM) as notifier:
            notifier.connect(address)
            notifier.sendall(payload)
    except OSError:
        return False
    return True


def _systemd_status(turn: Turn, tactic: CoreFarmer, accepted_tick: int) -> str:
    core = turn.core
    if core is None:
        core_status = "core respawning"
        core_health = "core_hp none; core_shield none"
    else:
        core_status = (
            f"core {core.position[0]}:{core.position[1]} "
            f"{core.view.state.value}; beacon_distance "
            f"{_distance(core.position, turn.beacon.position)}"
        )
        core_health = f"core_hp {core.hp}; core_shield {core.shield}"
    tuning_generation = os.environ.get("ARENA_TUNING_GENERATION", "0").strip() or "0"
    return (
        f"STATUS=tick {accepted_tick}; resources {turn.resources}/"
        f"{turn.resource_capacity}; workers {len(turn.workers)}; "
        f"fleet {len(turn.vanguards)}v/{len(turn.rangers)}r; "
        f"phase {tactic.strategy_phase(turn)}; {core_status}; "
        f"posture {tactic.threat_assessment.global_posture.value}; "
        f"threat {tactic.threat_assessment.level.value}; "
        f"threat_reason {tactic.threat_assessment.primary_reason}; "
        f"recovery {int(tactic.recovery_mode)}; "
        f"danger {len(tactic.last_danger_cells)}; "
        f"enemies {len(turn.visible_enemies)}; {core_health}; "
        f"worker_target {tactic.worker_target}; "
        f"beacon_policy {tactic.beacon_policy}; "
        f"compatibility_hold {int(tactic.compatibility_hold)}; "
        f"tuning_generation {tuning_generation}"
    )


def _has_significant_events(turn: Turn) -> bool:
    routine_events = {
        "CORE_MOVE_PROGRESS",
        "CORE_MOVE_STARTED",
        "CORE_MOVE_SUCCEEDED",
        "UNIT_MOVE_SUCCEEDED",
    }
    return any(event.event_type not in routine_events for event in turn.events)


def _should_log_turn(turn: Turn) -> bool:
    return (
        bool(turn.visible_enemies)
        or turn.tick % LOG_SNAPSHOT_INTERVAL == 0
        or _has_significant_events(turn)
    )


class _AcceptedTurnWatchdog:
    def __init__(self, game: ArenaHeroClient, timeout_seconds: float) -> None:
        self.game = game
        self.timeout_seconds = timeout_seconds
        self.stop_event = threading.Event()
        self.timed_out = threading.Event()
        self.lock = threading.Lock()
        self.last_accepted_at = time.monotonic()
        self.thread: threading.Thread | None = None

    def __enter__(self) -> _AcceptedTurnWatchdog:
        if self.timeout_seconds > 0:
            self.thread = threading.Thread(
                target=self._run,
                name="arena-accepted-turn-watchdog",
                daemon=True,
            )
            self.thread.start()
        return self

    def __exit__(self, *_args: object) -> None:
        self.stop_event.set()
        if self.thread is not None:
            self.thread.join(timeout=1.0)

    def mark_accepted(self) -> None:
        with self.lock:
            self.last_accepted_at = time.monotonic()

    def _run(self) -> None:
        poll_interval = min(1.0, max(0.05, self.timeout_seconds / 4))
        while not self.stop_event.wait(poll_interval):
            with self.lock:
                elapsed = time.monotonic() - self.last_accepted_at
            if elapsed < self.timeout_seconds:
                continue
            self.timed_out.set()
            print(
                "WARNING no accepted Turn received within "
                f"{self.timeout_seconds:g}s; restarting the Agent",
                file=sys.stderr,
                flush=True,
            )
            self.game.close()
            return


def _events_with_watchdog(
    game: ArenaHeroClient,
    watchdog: _AcceptedTurnWatchdog,
) -> Iterable[object]:
    """Convert a watchdog-triggered SDK close into a transient failure.

    The SDK reports a client closed by another thread as ``ConfigurationError``.
    That is a transport recovery condition here, not a bad deployment setting;
    preserving it as ``OSError`` lets systemd restart the Agent.
    """

    try:
        yield from game.events()
    except ArenaHeroError as exc:
        if watchdog.timed_out.is_set():
            raise OSError(
                "no accepted Turn received before the unattended recovery timeout"
            ) from exc
        raise


def play(
    api_key: str,
    *,
    base_url: str,
    worker_target: int,
    beacon_policy: str,
    compatibility_marker: Path | None = DEFAULT_COMPATIBILITY_MARKER,
    heartbeat_file: Path | None = None,
    stale_turn_timeout_seconds: float = DEFAULT_STALE_TURN_TIMEOUT_SECONDS,
) -> None:
    if (
        not math.isfinite(stale_turn_timeout_seconds)
        or stale_turn_timeout_seconds < 0
    ):
        raise ValueError("stale Turn timeout must be finite and zero or positive")
    tactic = CoreFarmer(
        worker_target=worker_target,
        beacon_policy=beacon_policy,
        compatibility_marker=compatibility_marker,
    )
    last_accepted_tick: int | None = None
    resource_ledger_snapshot: ResourceLedgerSnapshot | None = None
    with ArenaHeroClient(api_key=api_key, base_url=base_url) as game:
        watchdog = _AcceptedTurnWatchdog(game, stale_turn_timeout_seconds)
        with watchdog:
            for event in _events_with_watchdog(game, watchdog):
                if isinstance(event, Received):
                    if warning := _manual_override_summary(event):
                        print(warning, file=sys.stderr, flush=True)
                    continue
                if not isinstance(event, Turn):
                    continue
                turn = event
                if last_accepted_tick is not None and turn.tick <= last_accepted_tick:
                    print(
                        f"WARNING tick={turn.tick} duplicate_turn_ignored",
                        file=sys.stderr,
                        flush=True,
                    )
                    continue
                if resource_ledger_snapshot is not None:
                    _emit_resource_ledger(
                        _reconcile_resource_turn(resource_ledger_snapshot, turn)
                    )
                tactic.choose_actions(turn)
                try:
                    accepted = turn.submit()
                except APIError as exc:
                    if _is_turn_scoped_api_error(exc.error):
                        print(
                            f"WARNING tick={turn.tick} plan_skipped error={exc.error}",
                            file=sys.stderr,
                            flush=True,
                        )
                        continue
                    raise
                last_accepted_tick = accepted.tick
                watchdog.mark_accepted()
                resource_ledger_snapshot = _resource_ledger_snapshot(turn)
                _notify_systemd(
                    "WATCHDOG=1",
                    _systemd_status(turn, tactic, accepted.tick),
                )
                if heartbeat_file is not None:
                    write_heartbeat(
                        heartbeat_file,
                        tick=accepted.tick,
                        resources=turn.resources,
                        population=len(turn.units),
                        core_alive=turn.core is not None,
                    )
                if _should_log_turn(turn):
                    actions, events = _turn_diagnostics(turn)
                    print(
                        f"tick={accepted.tick} accepted={accepted.accepted} "
                        f"resources={turn.resources}/{turn.resource_capacity} "
                        f"workers={len(turn.workers)} vanguards={len(turn.vanguards)} "
                        f"rangers={len(turn.rangers)} cargo={sum(worker.cargo for worker in turn.workers)} "
                        f"visible_resources={len(turn.resource_cells)} actions={actions} events={events} "
                        f"recovery={int(tactic.recovery_mode)} phase={tactic.strategy_phase(turn)} "
                        f"worker_target={tactic.worker_target} "
                        f"beacon_policy={tactic.beacon_policy} "
                        f"tuning_generation={os.environ.get('ARENA_TUNING_GENERATION', '0').strip() or '0'} "
                        f"core_hp={turn.core.hp if turn.core else 'none'} "
                        f"core_shield={turn.core.shield if turn.core else 'none'} "
                        f"{_position_diagnostics(turn, tactic)}",
                        flush=True,
                    )
        if watchdog.timed_out.is_set():
            raise OSError(
                "no accepted Turn received before the unattended recovery timeout"
            )
    raise OSError("Arena Hero event stream ended unexpectedly")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Resource-first Arena Hero tactic.")
    parser.add_argument("--base-url", default=DEFAULT_BASE_URL)
    parser.add_argument("--env-file", type=Path)
    parser.add_argument("--worker-target", type=int, default=DEFAULT_WORKER_TARGET)
    parser.add_argument(
        "--beacon-policy",
        choices=("hold", "pursue", "retreat"),
        default=DEFAULT_BEACON_POLICY,
    )
    marker_group = parser.add_mutually_exclusive_group()
    marker_group.add_argument(
        "--compatibility-marker",
        type=Path,
        default=DEFAULT_COMPATIBILITY_MARKER,
        help="Path created by arena-hero-version-monitor when compatibility is unsafe.",
    )
    marker_group.add_argument(
        "--no-compatibility-marker",
        action="store_const",
        const=None,
        dest="compatibility_marker",
        help="Disable compatibility-marker checks (useful outside systemd).",
    )
    parser.add_argument(
        "--heartbeat-file",
        type=Path,
        help="Atomically write liveness metadata after every accepted Turn.",
    )
    parser.add_argument(
        "--stale-turn-timeout-seconds",
        type=float,
        default=DEFAULT_STALE_TURN_TIMEOUT_SECONDS,
        help="Exit transiently after this many seconds without an accepted Turn (0 disables).",
    )
    return parser


def _is_transient_api_error(exc: APIError) -> bool:
    return exc.status_code in {408, 429} or exc.status_code >= 500


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        api_key = load_api_key(env_file=args.env_file)
        play(
            api_key,
            base_url=args.base_url,
            worker_target=args.worker_target,
            beacon_policy=args.beacon_policy,
            compatibility_marker=args.compatibility_marker,
            heartbeat_file=args.heartbeat_file,
            stale_turn_timeout_seconds=args.stale_turn_timeout_seconds,
        )

    except KeyboardInterrupt:
        print("Arena Hero agent stopped.", file=sys.stderr)
        return 130
    except AuthenticationError:
        print("Arena Hero authentication failed. Rotate and replace the local API key.", file=sys.stderr)
        return AUTHENTICATION_EXIT_CODE
    except PolicyViolationError as exc:
        print(f"Arena Hero connection rejected by policy: {exc}", file=sys.stderr)
        return POLICY_EXIT_CODE
    except ProtocolError as exc:
        print(f"Arena Hero protocol mismatch; upgrade the official SDK: {exc}", file=sys.stderr)
        return PROTOCOL_EXIT_CODE
    except APIError as exc:
        print(f"Arena Hero API rejected the request: {exc.error}: {exc.message}", file=sys.stderr)
        return TRANSIENT_EXIT_CODE if _is_transient_api_error(exc) else API_EXIT_CODE
    except (TransportError, OSError) as exc:
        print(f"Arena Hero transient failure: {type(exc).__name__}: {exc}", file=sys.stderr)
        return TRANSIENT_EXIT_CODE
    except ValueError as exc:
        print(f"Arena Hero configuration error: {exc}", file=sys.stderr)
        return CONFIGURATION_EXIT_CODE
    except ArenaHeroError as exc:
        print(f"Arena Hero agent stopped: {type(exc).__name__}: {exc}", file=sys.stderr)
        return AGENT_EXIT_CODE
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
