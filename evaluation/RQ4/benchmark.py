#!/usr/bin/env python3
"""RQ4: five scraping configurations on the fixed, success-selected paper corpus."""
from pathlib import Path
import runpy
import sys

HERE = Path(__file__).resolve().parent
if __name__ == '__main__':
    # Reuse the measured runner, cancellation and checkpoint checks from RQ3/Scraping.
    sys.argv += ['--manifest', str(HERE / 'selection.json'), '--no-figures']
    if '--workers' not in sys.argv:
        sys.argv += ['--workers', '1']
    runpy.run_path(str(HERE.parent / 'Scraping/ablation.py'), run_name='__main__')
