#[cfg(test)]
#[macro_use]
extern crate approx;

use distr_traits::{normal::NormalSample, uniform::UniformSample};

/// PolynomialRing<N, T> is a polynomial ring of quotient ring.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct PolynomialRing<const N: usize, T> {
    coefficients: [T; N],
    // coefficients[i] is the coefficient of x^i
}

impl<const N: usize, T> PolynomialRing<N, T> {
    pub fn new(coefficients: [T; N]) -> Self {
        Self { coefficients }
    }
}

impl<const N: usize, T> std::ops::Index<usize> for PolynomialRing<N, T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        &self.coefficients[index]
    }
}

impl<const N: usize, T> std::ops::IndexMut<usize> for PolynomialRing<N, T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.coefficients[index]
    }
}

impl<const N: usize, T> From<T> for PolynomialRing<N, T>
where
    T: num_traits::identities::Zero + Copy,
{
    fn from(t: T) -> Self {
        let mut coefficients = [T::zero(); N];
        coefficients[0] = t;
        Self { coefficients }
    }
}

impl<const N: usize, T> From<[T; N]> for PolynomialRing<N, T> {
    fn from(coefficients: [T; N]) -> Self {
        Self { coefficients }
    }
}

impl<const N: usize, Left, Right> std::ops::Add<PolynomialRing<N, Right>> for PolynomialRing<N, Left>
where
    Left: std::ops::AddAssign<Right>,
{
    type Output = PolynomialRing<N, Left>;

    fn add(mut self, rhs: PolynomialRing<N, Right>) -> Self::Output {
        self.coefficients.iter_mut().zip(rhs.coefficients).for_each(|(l, r)| {
            *l += r;
        });
        self
    }
}

impl<const N: usize, Left, Right> std::ops::Sub<PolynomialRing<N, Right>> for PolynomialRing<N, Left>
where
    Left: std::ops::SubAssign<Right>,
{
    type Output = PolynomialRing<N, Left>;

    fn sub(mut self, rhs: PolynomialRing<N, Right>) -> Self::Output {
        self.coefficients.iter_mut().zip(rhs.coefficients).for_each(|(l, r)| {
            *l -= r;
        });
        self
    }
}

impl<const N: usize, Left, Right> std::ops::Mul<PolynomialRing<N, Right>> for PolynomialRing<N, Left>
where
    Left: std::ops::Mul<Right, Output = Left> + std::ops::AddAssign + std::ops::SubAssign + num_traits::identities::Zero + Copy,
    Right: Copy,
{
    type Output = PolynomialRing<N, Left>;

    fn mul(self, rhs: PolynomialRing<N, Right>) -> Self::Output {
        // TODO: use NTT
        
        let mut coefficients = [Left::zero(); N];
        for left_idx in 0..N {
            for right_idx in 0..N {
                if left_idx + right_idx < N {
                    coefficients[left_idx + right_idx] += self.coefficients[left_idx] * rhs.coefficients[right_idx];
                } else {
                    coefficients[left_idx + right_idx - N] -= self.coefficients[left_idx] * rhs.coefficients[right_idx];
                }
            }
        }

        Self::Output { coefficients }
    }
}

impl<const N: usize, T: NormalSample> NormalSample for PolynomialRing<N, T> {
    type Mean = T::Mean;
    type Variance = T::Variance;

    fn normal_sample(mean: Self::Mean, variance: Self::Variance, rng: &mut impl rand::Rng) -> Self {
        let coefficients = <[T; N] as NormalSample>::normal_sample(mean, variance, rng);
        Self::new(coefficients)
    }
}

impl<const N: usize, T: UniformSample> UniformSample for PolynomialRing<N, T> {
    fn uniform_sample(rng: &mut impl rand::Rng) -> Self {
        let coefficients = <[T; N] as UniformSample>::uniform_sample(rng);
        Self::new(coefficients)
    }
}

impl<const N: usize, T> std::fmt::Debug for PolynomialRing<N, T>
where
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "PolynomialRing({:?})", self.coefficients)
    }
}

impl<const N: usize, T> std::fmt::Display for PolynomialRing<N, T>
where
    T: std::fmt::Display + num_traits::identities::Zero,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut is_first = true;
        let mut is_printed = false;
        for (dim, cof) in self.coefficients.iter().enumerate().rev() {
            if cof.is_zero() {
                continue;
            }
            is_printed = true;

            if !is_first {
                write!(f, " + ")?;
            }
            is_first = false;
            if dim == 0 {
                write!(f, "{}", cof)?;
            } else if dim == 1 {
                write!(f, "{}x", cof)?;
            } else {
                write!(f, "{}x^{}", cof, dim)?;
            }
        }
        if !is_printed {
            write!(f, "0")?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        let a = PolynomialRing::new([1, 2, 3]);
        let b = PolynomialRing::new([4, 5, 6]);
        let c = a + b;
        assert_eq!(c.coefficients, [5, 7, 9]);
    }

    #[test]
    fn test_sub() {
        let a = PolynomialRing::new([1, 2, 3]);
        let b = PolynomialRing::new([4, 5, 6]);
        let c = a - b;
        assert_eq!(c.coefficients, [-3, -3, -3]);
    }

    #[test]
    fn test_mul() {
        let a = PolynomialRing::new([1, 0, 1]); // x^2 + 1
        let b = PolynomialRing::new([0, 1, 0]); // x
        let c = a * b; // x^3 + x % (x^2 + 1) = x - 1
        assert_eq!(c.coefficients, [-1, 1, 0]);
    }

    #[test]
    fn test_scalar_mul() {
        let a = PolynomialRing::new([1, 2, 3]);
        let b = 2;
        let c = a * b.into();
        assert_eq!(c.coefficients, [2, 4, 6]);
    }

    #[test]
    fn test_torus_1() {
        use fixed_torus::Torus;

        let a = PolynomialRing::new([Torus::from(0.7), Torus::from(1.4)]);
        let b = PolynomialRing::new([0, 1]);
        let c = a * b;
        // (0.4x + 0.7) * x = (0.4x^2 + 0.7x)
        // (0.4x^2 + 0.7x) % (x^2 + 1) = (0.7x - 0.4) = 0.7x + 0.6

        assert_relative_eq!(f64::from(c.coefficients[0]), 0.6, epsilon = 1e-6);
        assert_relative_eq!(f64::from(c.coefficients[1]), 0.7, epsilon = 1e-6);
    }

    #[test]
    fn test_torus_2() {
        use fixed_torus::Torus;

        let a = PolynomialRing::new([Torus::from(-0.1), Torus::from(0.3)]);
        let b = PolynomialRing::new([1, 3]);

        let c = a * b; // 0

        assert_relative_eq!(f64::from(c.coefficients[0]), 0.0, epsilon = 1e-6);
        assert_relative_eq!(f64::from(c.coefficients[1]), 1.0, epsilon = 1e-6); // 0 = 1
    }
}
