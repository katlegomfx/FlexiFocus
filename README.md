# FlexiAgent (coreAgent) README

## Overview

`coreAgent` is centered on `flexiFocus.py`, a local autonomous agent runtime with persistent state, structured tools, reviewer passes, background jobs, and an idle self-improvement workflow.

The main runtime is designed to run locally, keep durable state on disk, execute bounded tools, and generate proposal files for self-review rather than directly rewriting itself in place.

## Main Runtime: `flexiFocus.py`

`flexiFocus.py` is the primary agent loop. At a high level it provides:

- persistent runtime state under `.flexi/rlm_state`
- configurable LLM provider selection via `config.json`
- structured tool execution for shell, Python, tests, background tasks, project inspection, notebooks, databases, web fetches, and memory operations
- reviewer passes that can run after tools or tests and store results separately from raw tool output
- persistent goal tracking with active, pending, completed, cancelled, and failed states
- operator slash commands for runtime inspection
- idle proposal generation, staged review, bounded rewrites inside proposal files, and artifact retention

### Persistent state

By default, `flexiFocus.py` writes runtime state under `.flexi/rlm_state`.

Important files and folders include:

- `state.json`: primary state snapshot
- `full_archive.jsonl`: long-form archived history
- `response_trace.jsonl`: response and tool traces
- `snapshots/`: rolling snapshots
- `bg_task_logs/`: logs for managed background processes
- `config.json`: runtime configuration when using the default state layout
- `evolution_log.md`: proposal/evolution log entries

You can point the runtime at a different state location with `FLEXI_STATE_DIR`.

## Quick Start

Run the main agent from the repo root:

```bash
py .\flexiFocus.py
```

On non-Windows systems, `python3 flexiFocus.py` is the equivalent.

## Runtime Configuration

`flexiFocus.py` loads configuration from `config.json` and then applies environment-variable overrides.

Current runtime flags include:

- `idle_proposal_enabled`
- `idle_proposal_interval_seconds`
- `idle_proposal_auto_confirm`
- `reviewer_pass_enabled`
- `reviewer_pass_after_tools`
- `reviewer_pass_after_tests`
- `debug_startup`
- `no_dependency_check`

Environment overrides use the `FLEXI_` or `AGENT_` prefixes. For example, `FLEXI_IDLE_PROPOSAL_INTERVAL_SECONDS=600` overrides the config value at startup.

Useful startup flags:

- `--debug-startup`
- `--no-dependency-check`

## Interactive Runtime

The main loop starts an interactive session and shows an explicit prompt when user input is expected:

```text
[Awaiting user input] >
```

Built-in operator commands:

- `/health`: runtime health and status summary
- `/history`: recent runtime history summary
- `/reviews`: recent reviewer events
- `/goals`: list persisted goals
- `/goal`: inspect or update goal state
- `/help`: show operator command help

The runtime also persists goals across turns so active objectives can survive restarts.

## Tooling Surface

The agent exposes a broad Python-callable tool surface. Major groups include:

- shell and Python execution
- filesystem reads, writes, patches, and line edits
- workspace/project mapping and symbol search
- memory store and recall helpers
- Git inspection helpers
- notebook inspection and execution
- database schema/query helpers
- web/document fetch and summarization tools
- background process management
- validation helpers including compile/test flows
- subagent/task orchestration

Tool results are normalized into structured payloads with success state, summary text, warnings, errors, and data.

## Reviewer Passes

Reviewer passes are optional and configurable. They can run after tool execution or test execution and are stored separately from raw tool output so the runtime can distinguish:

- what a tool returned
- what the reviewer concluded about that output

This separation is important for later inspection through runtime history and review summaries.

## Idle Proposal Workflow

When the runtime is idle, it can generate and evaluate proposal files under `proposals/`.

The current workflow is staged and conservative:

1. Resume or inspect pending context.
2. Generate a proposal copy under `proposals/`.
3. Produce analysis and audit artifacts.
4. Build a change plan.
5. Generate a bounded rewrite plan.
6. Apply only targeted rewrites inside approved proposal sections.
7. Run pre-test review.
8. Run compile, review, and test checks.
9. Run final review.
10. Save a workflow trace and summary.

Important characteristics:

- rewrites are limited to approved sections such as the interactive loop, idle workflow helpers, and proposal evaluation paths
- rewrites target the proposal file, not the live runtime directly
- proposal artifacts are kept beside the proposal for inspection
- older artifact sets are rotated into `proposals/archive/`

### Proposal artifacts

For each generated proposal, the runtime can emit sidecar artifacts such as:

- `.analysis.md`
- `.audit.md`
- `.change-plan.md`
- `.rewrite-plan.json`
- `.rewrite-result.json`
- `.review-pre-test.md`
- `.review-final.md`
- `.workflow-trace.json`
- `.summary.md`

The summary artifact is intended to be the top-level entry point for reviewing a proposal run.

## Background Tasks

Background job support exists in two places:

- `flexiFocus.py` exposes runtime tools for spawning, checking, reading logs for, stopping, and restarting background tasks
- `bg_tasks.py` provides a reusable `BackgroundTask` and `BackgroundTaskManager`

`bg_tasks.py` now supports:

- task spawning and waiting
- heartbeat timestamps
- timeout handling
- stop and restart behavior
- log tail reads for inspection and tests

## Testing

The repository includes direct tests under `tests/`.

Typical local run:

```bash
py -m pytest -q
```

Inside `flexiFocus.py`, tool-driven pytest runs are executed through a direct subprocess path that disables third-party pytest plugin autoload. This keeps local repo tests focused on the repository itself instead of external machine-specific plugins.

## Notes and Caveats

- On Windows, the runtime now defaults to `cmd` for internal shell execution unless PowerShell is explicitly requested.
- Proposal generation is intentionally conservative: proposal files can be improved automatically, but live replacement remains bounded and review-oriented.
- Some long-term hardening work is still likely desirable, especially around state serialization, plugin/skill trust boundaries, and subprocess safety.
