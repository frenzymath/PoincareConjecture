import PoincareConjecture.Proofs.M14.Sec6_3_StablePrefix










set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₀ τ : ℝ} {x : G.Point}




theorem mem_jointDomain_of_stable_extension
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (H₀ : M14StableSet G T τ₀ x E)
    {Z : G.Horizontal x} (hZ : Z ∈ H₀.carrier) {c : ℝ} (hc : c ∈ Ioo 0 (Real.sqrt τ₀)) :
    (Z, c) ∈ M14JointDomain G E := by
  let U := H₀.carrier ×ˢ Ioo 0 (Real.sqrt τ₀)
  have hU : IsOpen U := H₀.carrier_open.prod isOpen_Ioo
  have hgraph : U ⊆ M14StableGraph G E := by
    rintro ⟨W, s⟩ ⟨hW, hs⟩
    have hτs : 0 < s ^ 2 := sq_pos_of_pos hs.1
    have hlt : s ^ 2 < τ₀ := by
      have h := (sq_lt_sq₀ hs.1.le (Real.sqrt_nonneg τ₀)).mpr hs.2
      simpa only [Real.sq_sqrt H₀.tau_pos.le] using h
    have hstable := stableInitialVector_prefix hCoordinates hM04 hM12 E hτs hlt
      ((H₀.carrier_exact W).mp hW)
    obtain ⟨H⟩ := stableSet_nonempty E hτs ⟨W, hstable.choose⟩
    exact ⟨s ^ 2, H, hτs, (H.carrier_exact W).mpr hstable, (Real.sqrt_sq hs.1.le).symm⟩
  exact ⟨hgraph ⟨hZ, hc⟩, U, hU, ⟨hZ, hc⟩, fun _ hz => hgraph hz.1⟩




theorem strictPrefix
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (H₀ : M14StableSet G T τ₀ x E)
    (hτ : 0 < τ) (hlt : τ < τ₀) (_hallowed : T - τ ∈ I.domain)
    (Z : G.Horizontal x) (hZ : Z ∈ H₀.carrier) :
    ∃ H : M14StableSet G T τ x E,
      Z ∈ H.carrier ∧ (Z, Real.sqrt τ) ∈ M14JointDomain G E := by
  have hstable := stableInitialVector_prefix hCoordinates hM04 hM12 E hτ hlt
    ((H₀.carrier_exact Z).mp hZ)
  obtain ⟨H⟩ := stableSet_nonempty E hτ ⟨Z, hstable.choose⟩
  exact ⟨H, (H.carrier_exact Z).mpr hstable,
    mem_jointDomain_of_stable_extension hCoordinates hM04 hM12 E H₀ hZ
      ⟨Real.sqrt_pos.mpr hτ, Real.sqrt_lt_sqrt hτ.le hlt⟩⟩

end PoincareConjecture.M14
