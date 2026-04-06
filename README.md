# FlexiAgent (coreAgent)

`coreAgent` is a local, stateful agent framework built around `flexiFocus.py`.

It is designed for people who want to run an autonomous coding and operations assistant on their own machine, inspect what it is doing, and let it manage work through a controlled interactive loop instead of a black-box hosted service.

## What It Does

`flexiFocus.py` combines several capabilities in one runtime:

- interactive local agent loop
- persistent memory and history under `.flexi/rlm_state`
- structured tool execution for shell, Python, filesystem, project inspection, notebooks, databases, and web fetches
- reviewer passes that summarize runtime actions separately from raw tool output
- persisted goals and operator slash commands
- idle self-improvement workflow that writes proposals under `proposals/` instead of rewriting the live runtime directly

The project is best understood as an experimental local agent framework rather than a polished end-user app.

## Why This Repo Is Useful

If you want to study or extend a local autonomous agent, this repo gives you:

- a single-file primary runtime with visible control flow
- durable local state instead of stateless chat only
- explicit runtime prompts and operator commands
- built-in trace and artifact generation for introspection
- conservative proposal-based self-improvement instead of silent self-mutation

## Quick Start

Prerequisites:

- Python 3.11 or newer
- a terminal on the local machine where the agent will run
- optional access to GitHub Copilot authentication if you want to use the default provider flow

From the repo root, start the agent with:

```bash
py .\flexiFocus.py
```

On Linux or macOS, use:

```bash
python3 flexiFocus.py
```

When the runtime is ready, it prompts with:

```text
[Awaiting user input] >
```

## First Run Expectations

On first launch, the runtime may:

- create `.flexi/rlm_state`
- create or load `config.json`
- warn about optional platform dependencies such as `pywin32`, `psutil`, `Pillow`, or `mss`
- ask you to authenticate for the configured LLM provider if no cached token is available

This is normal. The runtime is intentionally explicit about missing capabilities instead of failing silently.

If an optional package is missing, the runtime should still start, but some tools may be unavailable until you install the corresponding dependency.

## Example Things To Try

After launch, try prompts like:

- `Summarize this workspace.`
- `Show me the highest-risk files in this repo.`
- `Inspect the current Python environment.`
- `Create a plan to improve the runtime safely.`
- `Explain the active goals and current state.`

You can also use operator commands directly:

- `/health`
- `/history`
- `/reviews`
- `/goals`
- `/goal add <text>`
- `/help`

## Runtime Model

`flexiFocus.py` is the main runtime. At a high level it provides:

- persistent runtime state under `.flexi/rlm_state`
- configurable LLM provider selection via `config.json`
- structured tool execution for shell, Python, background processes, project inspection, notebooks, databases, web fetches, and memory operations
- reviewer passes that can run after runtime actions and store results separately from raw tool output
- persistent goal tracking with active, pending, completed, cancelled, and failed states
- operator slash commands for runtime inspection
- idle proposal generation, staged review, bounded rewrites inside proposal files, and artifact retention

## Configuration

`flexiFocus.py` loads configuration from `config.json` and then applies environment-variable overrides.

Current runtime flags include:

- `idle_proposal_enabled`
- `idle_proposal_interval_seconds`
- `idle_proposal_auto_confirm`
- `reviewer_pass_enabled`
- `reviewer_pass_after_tools`
- `debug_startup`
- `no_dependency_check`

Environment overrides use the `FLEXI_` or `AGENT_` prefixes. For example:

```powershell
$env:FLEXI_IDLE_PROPOSAL_INTERVAL_SECONDS = "600"
```

Useful startup flags:

- `--debug-startup`
- `--no-dependency-check`

## State And Files

By default, the runtime writes state under `.flexi/rlm_state`.

Important files and folders include:

- `state.json`: primary state snapshot
- `full_archive.jsonl`: long-form archived history
- `response_trace.jsonl`: response and tool traces
- `snapshots/`: rolling snapshots
- background process logs: runtime logs for managed background processes
- `config.json`: runtime configuration when using the default state layout
- `evolution_log.md`: proposal and evolution log entries

You can point the runtime at a different state location with `FLEXI_STATE_DIR`.

## Tooling Surface

The agent exposes a broad Python-callable tool surface. Major groups include:

- shell and Python execution
- filesystem reads, writes, patches, and line edits
- workspace and project mapping
- memory store and recall helpers
- Git inspection helpers
- notebook inspection and execution
- database schema and query helpers
- web and documentation fetch helpers
- background process management
- runtime inspection helpers
- subagent orchestration

Tool results are normalized into structured payloads with success state, summary text, warnings, errors, and data.

## Reviewer Passes

Reviewer passes are optional and configurable. They can run after runtime actions and are stored separately from raw tool output so the runtime can distinguish:

- what a tool returned
- what the reviewer concluded about that output

This makes it easier to inspect execution history without mixing raw output and evaluation into the same record.

## Idle Proposal Workflow

When the runtime is idle, it can generate and evaluate proposal files under `proposals/`.

The current workflow is staged and conservative:

1. Resume or inspect pending context.
2. Generate a proposal copy under `proposals/`.
3. Produce analysis and audit artifacts.
4. Build a change plan.
5. Generate a bounded rewrite plan.
6. Apply only targeted rewrites inside approved proposal sections.
7. Run a review pass on the updated proposal.
8. Run proposal evaluation and gating checks.
9. Run final review.
10. Save a workflow trace and summary.

Important characteristics:

- rewrites are limited to approved sections such as the interactive loop, idle workflow helpers, and proposal evaluation paths
- rewrites target the proposal file, not the live runtime directly
- proposal artifacts are kept beside the proposal for inspection
- older artifact sets are rotated into `proposals/archive/`

### Proposal Artifacts

For each generated proposal, the runtime can emit sidecar artifacts such as:

- `.analysis.md`
- `.audit.md`
- `.change-plan.md`
- `.rewrite-plan.json`
- `.rewrite-result.json`
- `.review-final.md`
- `.workflow-trace.json`
- `.summary.md`

The summary artifact is intended to be the top-level entry point when reviewing a proposal run.

## Project Layout

Useful top-level files and folders:

- `flexiFocus.py`: main runtime
- `proposals/`: generated proposal files and sidecar artifacts
- `.flexi/rlm_state/`: runtime state, history, and traces

## When To Use This Repo

This repo is most useful if you want to:

- study how a local stateful agent can be built without hiding the control loop
- experiment with proposal-driven self-improvement instead of direct self-rewrites
- extend a Python agent runtime with additional tools, reviewers, or persistence logic
- inspect real execution traces and state artifacts while the agent runs


## Caveats

- On Windows, the runtime defaults to `cmd` for internal shell execution unless PowerShell is explicitly requested.
- The project is experimental and stateful; it is not a sandboxed production agent platform.
- Proposal generation is intentionally conservative: proposal files can be improved automatically, but live replacement remains bounded and review-oriented.
- Some long-term hardening work is still likely desirable, especially around state serialization, plugin and skill trust boundaries, and subprocess safety.
