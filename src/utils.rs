use ff::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Region, Value},
    plonk::{Advice, Column, Error, Fixed},
};

/// 为 `enabled` selector 赋 F::ONE，为 `unenabled` selector 赋 F::ZERO。
/// 两者的 union 将被实际写入。
pub fn enable_fixed_selectors<F: Field>(
    region: &mut Region<'_, F>,
    annotation_prefix: &str,
    enabled: &[Column<Fixed>],
    unenabled: &[Column<Fixed>],
    offset: usize,
) -> Result<(), Error> {
    for (i, selector) in enabled.iter().enumerate() {
        region.assign_fixed(
            || format!("{} - enabled selector {}", annotation_prefix, i),
            *selector,
            offset,
            || Value::known(F::ONE),
        )?;
    }

    for (i, selector) in unenabled.iter().enumerate() {
        region.assign_fixed(
            || format!("{} - unenabled selector {}", annotation_prefix, i),
            *selector,
            offset,
            || Value::known(F::ZERO),
        )?;
    }

    Ok(())
}

pub fn assign_fixed_batch<F: Field>(
    region: &mut Region<'_, F>,
    columns: &[Column<Fixed>],
    annotations: Option<&[&str]>,
    values: &[F],
    offset: usize,
) -> Result<(), Error> {
    assert_eq!(
        columns.len(),
        values.len(),
        "Fixed column count and value count mismatch"
    );

    if let Some(ann) = annotations {
        assert_eq!(
            ann.len(),
            columns.len(),
            "Annotation count must match column count"
        );
        for ((col, val), label) in columns.iter().zip(values.iter()).zip(ann.iter()) {
            region.assign_fixed(|| label.to_string(), *col, offset, || Value::known(*val))?;
        }
    } else {
        for (i, (col, val)) in columns.iter().zip(values.iter()).enumerate() {
            region.assign_fixed(
                || format!("fixed {}", i),
                *col,
                offset,
                || Value::known(*val),
            )?;
        }
    }

    Ok(())
}

pub fn assign_advice_batch<F: Field>(
    region: &mut Region<'_, F>,
    columns: &[Column<Advice>],
    annotations: Option<&[&str]>,
    values: &[F],
    offset: usize,
) -> Result<Vec<AssignedCell<F, F>>, Error> {
    assert_eq!(
        columns.len(),
        values.len(),
        "Advice column count and value count mismatch"
    );

    let mut assigned_cells = Vec::with_capacity(columns.len());

    if let Some(ann) = annotations {
        assert_eq!(
            ann.len(),
            columns.len(),
            "Annotation count must match column count"
        );
        for ((col, val), label) in columns.iter().zip(values.iter()).zip(ann.iter()) {
            let cell =
                region.assign_advice(|| label.to_string(), *col, offset, || Value::known(*val))?;
            assigned_cells.push(cell);
        }
    } else {
        for (col, val) in columns.iter().zip(values.iter()) {
            let cell = region.assign_advice(|| "", *col, offset, || Value::known(*val))?;
            assigned_cells.push(cell);
        }
    }

    Ok(assigned_cells)
}
