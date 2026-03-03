"""
D=1 Metric Ratio Benchmark
===========================

Computes the D=1 metric for finite sets, measuring how far FinSet objects
are from the fixed-point condition D^D = D (i.e., the internal hom
collapsing to the identity).

Connection to the Lean verification:
  The Lean4 formalization in FixedPoint/ proves that for certain locally
  presentable categories, a fixed point F(X) = X exists (Lambek/Adamek).
  This benchmark gives the numerical intuition for WHY finite sets never
  achieve that fixed point: the self-hom n^n grows super-exponentially
  relative to n, so the D=1 metric d(D, D^D) = 1 - 1/n^(n-1) approaches
  1 (maximum distance). Infinite objects in locally presentable categories
  can achieve d = 0.

Usage:
  python3 Benchmarks/d1_ratio.py
"""

from decimal import Decimal, getcontext


def main():
    # Use enough precision to show the metric never actually reaches 1.
    getcontext().prec = 50

    # Pre-compute all rows so we can size columns to fit the data.
    rows = []
    for n in range(2, 21):
        dd = n ** n                         # |D^D|
        ratio = n ** (n - 1)                # |D^D| / |D|
        # Exact rational arithmetic: 1 - 1/ratio via Decimal.
        d_metric = Decimal(1) - Decimal(1) / Decimal(ratio)
        rows.append((n, dd, ratio, d_metric))

    # Format the metric column: show enough digits to see the non-1 tail.
    # We display 1 - 1/n^(n-1) as "1 - 1/n^(n-1)" string for large n,
    # or as a decimal for small n. Simpler: just use a fixed format width
    # with enough decimal places.
    metric_strs = []
    for _, _, ratio, d_metric in rows:
        # Show as many digits as needed. For readability, cap at 30 decimals.
        s = format(d_metric, "f")
        # Decimal "f" format may produce very long strings; trim to 30 places.
        if "." in s:
            int_part, frac_part = s.split(".")
            frac_part = frac_part[:30]
            # Strip trailing zeros but keep at least one digit after dot.
            frac_part = frac_part.rstrip("0") or "0"
            s = f"{int_part}.{frac_part}"
        metric_strs.append(s)

    # Column widths: at least as wide as the header, or the widest value.
    header_n = "n"
    header_dd = "|D^D| = n^n"
    header_ratio = "ratio = n^(n-1)"
    header_metric = "d(D, D^D)"

    col_n = max(len(header_n), max(len(str(r[0])) for r in rows))
    col_dd = max(len(header_dd), max(len(f"{r[1]:,}") for r in rows))
    col_ratio = max(len(header_ratio), max(len(f"{r[2]:,}") for r in rows))
    col_metric = max(len(header_metric), max(len(s) for s in metric_strs))

    total = col_n + 2 + col_dd + 2 + col_ratio + 2 + col_metric

    print("D=1 Metric: FinSet Divergence from Fixed Point")
    print("=" * total)
    print()
    print(
        f"{header_n:>{col_n}}  "
        f"{header_dd:>{col_dd}}  "
        f"{header_ratio:>{col_ratio}}  "
        f"{header_metric:>{col_metric}}"
    )
    print(
        f"{'-' * col_n}  "
        f"{'-' * col_dd}  "
        f"{'-' * col_ratio}  "
        f"{'-' * col_metric}"
    )

    for (n, dd, ratio, _), ms in zip(rows, metric_strs):
        print(
            f"{n:>{col_n}}  "
            f"{dd:>{col_dd},}  "
            f"{ratio:>{col_ratio},}  "
            f"{ms:>{col_metric}}"
        )

    print()
    print("Observations:")
    print("  - ratio = n^(n-1) grows super-exponentially.")
    print("  - d(D, D^D) -> 1 as n -> infinity (maximum distance).")
    print("  - d is strictly less than 1 for every finite n (never a fixed point).")
    print("  - FinSet objects never reach the fixed point D^D = D.")
    print("  - In locally presentable categories with infinite objects,")
    print("    Adamek's theorem guarantees a fixed point where d = 0.")


if __name__ == "__main__":
    main()
