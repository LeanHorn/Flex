# Scraping measurement internals

The reproducible paper experiment is documented in
[**RQ4: qualifier scraping**](../RQ4/README.md).
Use that entry point for the fixed 391-CHC population, clean setup, five
configurations, progress/resume commands, measurements, and data export.
It reconstructs inputs from `flex-benchmarks`; no local screening run is needed.

This directory retains the shared measurement machinery:

- `ablation.py`: frozen trials, checkpoints, resource accounting and resume.
- `report.py`: detailed CSV/JSON extraction from events and diagnostics.
- `benchmark.py`: earlier screening runner; not needed to reproduce RQ4.
- `paper_appendix.py`: plotting helpers and the historical local appendix
  generator. Its command-line mode asserts the old local counts; use
  `evaluation/RQ4/report.py` for fresh measurements.

Previous experiments contain frozen copies of their original runners and
instructions. Their raw measurements are unchanged.
