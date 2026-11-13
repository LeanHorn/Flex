# Scraping measurement internals

The reproducible paper experiment is documented in
[**RQ4: qualifier scraping**](../RQ4/README.md).
Use that entry point for the fixed 391-CHC population, clean setup, five
configurations, progress/resume commands, measurements, and data export.
It reconstructs inputs from `flex-benchmarks`; no earlier screening run is needed.

This directory retains the shared measurement machinery:

- `ablation.py`: frozen trials, checkpoints, resource accounting and resume.
- `report.py`: detailed CSV/JSON extraction from events and diagnostics.
- `benchmark.py`: earlier screening runner; not needed to reproduce RQ4.
- `paper_appendix.py`: plotting helpers used by `evaluation/RQ4/report.py --figures`.
  Its own command-line mode is legacy; use `evaluation/RQ4/report.py` for new results.

Previous experiments contain frozen copies of their original runners and
instructions. Their raw measurements are unchanged.
