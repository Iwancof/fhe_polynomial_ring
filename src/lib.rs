/// PolynomialRing<N, T> is a polynomial ring of quotient ring.
pub struct PolynomialRing<const N: usize, T> {
    coefficients: [T; N],
}

impl<const N: usize, T> PolynomialRing<N, T> {
    pub fn new(coefficients: [T; N]) -> Self {
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
}
