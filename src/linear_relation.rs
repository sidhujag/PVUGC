use ark_ff::PrimeField;

/// Find coefficients `s` such that `sum_i s_i * errors[i] = 0` and `sum_i s_i != 0`.
/// Returns one such non-trivial relation, or `None` if not found.
pub fn find_relation_with_nonzero_sum<F: PrimeField>(errors: &[Vec<F>]) -> Option<Vec<F>> {
    if errors.is_empty() {
        return None;
    }
    let rows_n = errors[0].len();
    let cols_n = errors.len();
    if cols_n == 0 || rows_n == 0 {
        return None;
    }
    if errors.iter().any(|v| v.len() != rows_n) {
        return None;
    }

    // Matrix with error vectors as columns: rows_n x cols_n
    let mut mat = vec![vec![F::zero(); cols_n]; rows_n];
    for (c, v) in errors.iter().enumerate() {
        for r in 0..rows_n {
            mat[r][c] = v[r];
        }
    }

    // RREF over rows to get nullspace basis for mat * s = 0.
    let mut pivot_cols: Vec<usize> = Vec::new();
    let mut pivot_row = 0usize;
    for col in 0..cols_n {
        let mut found = None;
        for r in pivot_row..rows_n {
            if !mat[r][col].is_zero() {
                found = Some(r);
                break;
            }
        }
        let Some(rp) = found else {
            continue;
        };
        mat.swap(pivot_row, rp);
        let inv = mat[pivot_row][col].inverse()?;
        for j in col..cols_n {
            mat[pivot_row][j] *= inv;
        }
        for r in 0..rows_n {
            if r == pivot_row {
                continue;
            }
            let factor = mat[r][col];
            if factor.is_zero() {
                continue;
            }
            let pivot_slice = mat[pivot_row][col..cols_n].to_vec();
            for j in col..cols_n {
                mat[r][j] -= factor * pivot_slice[j - col];
            }
        }
        pivot_cols.push(col);
        pivot_row += 1;
        if pivot_row == rows_n {
            break;
        }
    }

    let mut is_pivot_col = vec![false; cols_n];
    for &c in &pivot_cols {
        is_pivot_col[c] = true;
    }
    let free_cols: Vec<usize> = (0..cols_n).filter(|&c| !is_pivot_col[c]).collect();
    if free_cols.is_empty() {
        return None;
    }

    // Try nullspace basis vectors and return one with non-zero coefficient sum.
    for &free in &free_cols {
        let mut s = vec![F::zero(); cols_n];
        s[free] = F::one();
        for (r, &pc) in pivot_cols.iter().enumerate().rev() {
            let mut acc = F::zero();
            for j in (pc + 1)..cols_n {
                if !mat[r][j].is_zero() {
                    acc += mat[r][j] * s[j];
                }
            }
            s[pc] = -acc;
        }
        let sum_s = s.iter().fold(F::zero(), |acc, x| acc + *x);
        if !sum_s.is_zero() {
            return Some(s);
        }
    }
    None
}
