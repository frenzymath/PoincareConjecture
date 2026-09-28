import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Chain.Maximal

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.CapCertificate.IsOutgoingChain

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} {C : CapCertificate g} {H : ConnectedNeckCapCover g}
  {T : BalancedNeckChain g C.epsilon}

theorem shape_eq_finite_or_forward (hT : C.IsOutgoingChain H T) :
    (∃ b, T.shape = .finite 0 b) ∨ T.shape = .forward 0 := by
  have hz := hT.zero_active
  cases hs : T.shape with
  | finite a b =>
    have hab : a ≤ 0 ∧ 0 ≤ b := by simpa only [hs, ChainShape.active, mem_Icc] using hz
    have ha := hT.nonnegative a (by simp only [hs, ChainShape.active, mem_Icc]; omega)
    have ha0 : a = 0 := by omega
    exact Or.inl ⟨b, by rw [ha0]⟩
  | forward a =>
    have ha0 : a ≤ 0 := by simpa only [hs, ChainShape.active, mem_Ici] using hz
    have ha := hT.nonnegative a (by simp [hs, ChainShape.active])
    have heq : a = 0 := by omega
    exact Or.inr (by rw [heq])
  | backward b =>
    have hb : 0 ≤ b := by simpa only [hs, ChainShape.active, mem_Iic] using hz
    have hn := hT.nonnegative (-1) (by simp only [hs, ChainShape.active, mem_Iic]; omega)
    omega
  | biInfinite =>
    have hn := hT.nonnegative (-1) (by simp [hs, ChainShape.active])
    omega

theorem shape_eq_finite_of_right_endpoint (hT : C.IsOutgoingChain H T)
    {b : ℤ} (hb : b ∈ T.shape.active) (hnext : b + 1 ∉ T.shape.active) :
    T.shape = .finite 0 b := by
  rcases hT.shape_eq_finite_or_forward with ⟨c, hs⟩ | hs
  · have hb' : 0 ≤ b ∧ b ≤ c := by simpa only [hs, ChainShape.active, mem_Icc] using hb
    have hnext' : ¬ (0 ≤ b + 1 ∧ b + 1 ≤ c) := by
      simpa only [hs, ChainShape.active, mem_Icc] using hnext
    have hcb : c = b := by omega
    exact hcb ▸ hs
  · have hb' : 0 ≤ b := by simpa only [hs, ChainShape.active, mem_Ici] using hb
    have hnext' : ¬ 0 ≤ b + 1 := by
      simpa only [hs, ChainShape.active, mem_Ici] using hnext
    omega

end PoincareConjecture.CapCertificate.IsOutgoingChain
