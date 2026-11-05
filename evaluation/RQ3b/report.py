"""Generate RQ3b reports with the shared coverage and timing definitions."""
from pathlib import Path
import runpy

if __name__ == '__main__':
    runpy.run_path(str(Path(__file__).resolve().parents[1] / 'RQ3a' / 'report.py'),
                  run_name='__main__')
