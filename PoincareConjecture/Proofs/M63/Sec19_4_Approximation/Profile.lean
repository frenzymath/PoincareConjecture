import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.ProfilePrimitive








set_option autoImplicit false

namespace PoincareConjecture



theorem m63ProfileProperties {N : ℕ} (hN : 0 < N) : M63ProfileProperties N where
  normalization_positive := m63ProfileBase_integral_pos hN
  smooth := m63Profile_smooth N
  periodic := m63Profile_periodic hN
  nonnegative := m63Profile_nonneg hN
  positive := fun _ hx => m63Profile_pos hN hx
  symmetric := m63Profile_symmetric hN
  monotone_half := m63Profile_monotone_half hN
  flat := m63Profile_flat hN
  cell_integral := m63Profile_cell_integral hN
  flattening_smooth := m63Flattening_smooth N
  flattening_derivative := m63Flattening_hasDerivAt N
  flattening_strictMono := m63Flattening_strictMono hN
  flattening_zero := m63Flattening_zero N
  flattening_cell_shift := m63Flattening_cell_shift hN
  flattening_period_shift := m63Flattening_period_shift hN
  circle_homeomorph := m63Flattening_circle_homeomorph hN

end PoincareConjecture
