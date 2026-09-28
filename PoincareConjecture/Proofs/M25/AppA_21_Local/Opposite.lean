import PoincareConjecture.Proofs.M25.Mathlib.OppositeCollarComponents
import PoincareConjecture.Proofs.M25.AppA_1_Necks.Coordinates

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

private noncomputable def levelCollar (N : EpsilonNeck g) {s r : ℝ}
    (hlo : -N.epsilon⁻¹ < s - r) (hhi : s + r < N.epsilon⁻¹) :
    (UnitTwoSphere × Ioo (-r) r) ≃ₜ N.region (s - r) (s + r) where
  toFun z := ⟨N.coordinate_map (z.1, s + z.2), by
    have hz : s + (z.2 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      constructor <;> linarith [z.2.property.1, z.2.property.2]
    refine ⟨N.coordinate_map_mem ⟨mem_univ _, hz⟩, ?_⟩
    rw [N.coordinate_inverse_map _ hz]
    change s - r < s + (z.2 : ℝ) ∧ s + (z.2 : ℝ) < s + r
    constructor <;> linarith [z.2.property.1, z.2.property.2]⟩
  invFun x := ((N.coordinate_inverse x).1,
    ⟨(N.coordinate_inverse x).2 - s, by
      constructor <;> linarith [x.property.2.1, x.property.2.2]⟩)
  left_inv z := by
    have hz : s + (z.2 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      constructor <;> linarith [z.2.property.1, z.2.property.2]
    apply Prod.ext
    · change (N.coordinate_inverse (N.coordinate_map (z.1, s + (z.2 : ℝ)))).1 = z.1
      exact congrArg Prod.fst (N.coordinate_inverse_map (z.1, s + (z.2 : ℝ)) hz)
    · apply Subtype.ext
      change (N.coordinate_inverse (N.coordinate_map (z.1, s + (z.2 : ℝ)))).2 - s = _
      rw [N.coordinate_inverse_map _ hz]
      dsimp only
      ring
  right_inv x := by
    apply Subtype.ext
    change N.coordinate_map ((N.coordinate_inverse x).1,
      s + ((N.coordinate_inverse x).2 - s)) = x
    rw [show s + ((N.coordinate_inverse x).2 - s) = (N.coordinate_inverse x).2 by ring]
    exact N.coordinate_map_inverse x.property.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply N.coordinate_map_smooth.continuousOn.comp_continuous
      (continuous_fst.prodMk (continuous_const.add
        (continuous_subtype_val.comp continuous_snd)))
    intro z
    refine ⟨mem_univ _, ?_⟩
    change s + (z.2 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
    constructor <;> linarith [z.2.property.1, z.2.property.2]
  continuous_invFun := by
    have hc : Continuous (fun x : N.region (s - r) (s + r) => N.coordinate_inverse x) :=
      N.coordinate_inverse_smooth.continuousOn.comp_continuous continuous_subtype_val
        (fun x => x.property.1)
    exact hc.fst.prodMk ((hc.snd.sub continuous_const).subtype_mk _)

theorem opposite_level_components
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    (N : EpsilonNeck g) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    let S := range (fun q : UnitTwoSphere => N.coordinate_map (q, s))
    ∀ a b : M, a ∉ S → b ∉ S →
      connectedComponentIn Sᶜ a ≠ connectedComponentIn Sᶜ b →
      S ⊆ frontier (connectedComponentIn Sᶜ a) ∩
        frontier (connectedComponentIn Sᶜ b) →
      frontier (connectedComponentIn Sᶜ a) = S ∧
        frontier (connectedComponentIn Sᶜ b) = S ∧
        IsClopen (connectedComponentIn Sᶜ a ∪ S ∪ connectedComponentIn Sᶜ b) ∧
        IsConnected (connectedComponentIn Sᶜ a ∪ S ∪ connectedComponentIn Sᶜ b) ∧
        connectedComponentIn Sᶜ a ∪ S ∪ connectedComponentIn Sᶜ b =
          connectedComponent a := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  dsimp only
  intro a b ha hb hne hfront
  have hm : 0 < min (s + N.epsilon⁻¹) (N.epsilon⁻¹ - s) := by
    apply lt_min <;> linarith [hs.1, hs.2]
  obtain ⟨r, hr, hsmall⟩ := exists_between hm
  have hlo : -N.epsilon⁻¹ < s - r := by linarith [(lt_min_iff.mp hsmall).1]
  have hhi : s + r < N.epsilon⁻¹ := by linarith [(lt_min_iff.mp hsmall).2]
  let e := N.levelCollar hlo hhi
  have he : range (fun q : UnitTwoSphere =>
      (e (q, ⟨0, neg_lt_zero.mpr hr, hr⟩) : M)) =
      range (fun q : UnitTwoSphere => N.coordinate_map (q, s)) := by
    congr 1
    funext q
    change N.coordinate_map (q, s + 0) = N.coordinate_map (q, s)
    rw [add_zero]
  have h := Poincare.Topology.opposite_collar_components hr
    (N.isOpen_region (s - r) (s + r)) e (a := a) (b := b)
  dsimp only at h
  rw [he] at h
  exact h ha hb hne hfront

end PoincareConjecture.EpsilonNeck
