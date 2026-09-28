import PoincareConjecture.Proofs.M76.Wall.Mathlib.PLLocalDeterminantSign
import PoincareConjecture.Proofs.M76.Mathlib.LocalPLAffineHalfspacePasting
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse
import Mathlib.Topology.OpenPartialHomeomorph.Constructions













set_option autoImplicit false

open Set Metric

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]



theorem plLocalSign_eq_one_of_halfspace_fixed
    (h : OpenPartialHomeomorph E E) (hh : h ∈ piecewiseAffineGroupoid E)
    (ell : E →ᴬ[ℝ] ℝ) (v : E) (hv : ell.contLinear v = 1)
    (hside : ∀ y ∈ h.source, 0 ≤ ell (h y) ↔ 0 ≤ ell y)
    (hfix : ∀ y ∈ h.source, ell y = 0 → h y = y)
    (x : h.source) (hx : ell x = 0) : plLocalSign h hh x = 1 := by
  classical
  let Hplus : Set E := {y | 0 ≤ ell y}
  let ident := OpenPartialHomeomorph.ofSet h.source h.open_source
  have himage : h.IsImage Hplus Hplus := fun _ hy => hside _ hy
  have hiimage : ident.IsImage Hplus Hplus := fun _ _ => Iff.rfl
  have hagree : EqOn h ident (h.source ∩ frontier Hplus) := by
    intro y hy
    have hz := ell.continuous.frontier_preimage_subset (Ici 0) hy.2
    have hell : ell y = 0 := by simpa [frontier_Ici] using hz
    exact hfix y hy.1 hell
  let g := h.piecewise ident Hplus Hplus himage hiimage rfl hagree
  have hgs : g.source = h.source := by
    ext y
    change (y ∈ h.source ∧ y ∈ Hplus ∨ y ∈ h.source ∧ y ∉ Hplus) ↔ _
    tauto
  have hgmap (y : E) : g y = if 0 ≤ ell y then h y else y := rfl
  have hg : g ∈ piecewiseAffineGroupoid E := by
    apply (mem_piecewiseAffineGroupoid_iff_forward g).mpr
    rw [hgs]
    exact ((mem_piecewiseAffineGroupoid_iff_forward h).mp hh).affine_halfspace_paste
      (locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ E) h.open_source)
      ell.toAffineMap hfix
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (h.open_source.mem_nhds x.property)
  let t : ℝ := r / (2 * (‖v‖ + 1))
  have ht : 0 < t := div_pos hr (by positivity)
  have htr : t * ‖v‖ < r := by
    have heq : t * (2 * (‖v‖ + 1)) = r := by
      dsimp [t]
      exact div_mul_cancel₀ _ (by positivity)
    nlinarith [norm_nonneg v]
  have hpos : x.val + t • v ∈ ball x.val r := by
    simpa [mem_ball, dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos ht] using htr
  have hneg : x.val + (-t) • v ∈ ball x.val r := by
    simpa [mem_ball, dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos ht] using htr
  have hheight (a : ℝ) : ell (x.val + a • v) = a := by
    rw [add_comm]
    change ell (a • v +ᵥ x.val) = a
    rw [ell.map_vadd]
    simp [hv, hx]
  let j : ball x.val r → h.source := fun z => ⟨z, hball z.property⟩
  let k : ball x.val r → g.source := fun z => ⟨z, hgs.symm ▸ hball z.property⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hk : Continuous k := continuous_subtype_val.subtype_mk _
  have hhs := (isLocallyConstant_plLocalSign h hh).comp_continuous hj
  have hgg := (isLocallyConstant_plLocalSign g hg).comp_continuous hk
  let : PreconnectedSpace (ball x.val r) :=
    Subtype.preconnectedSpace (convex_ball x.val r).isPreconnected
  let xp : ball x.val r := ⟨x.val + t • v, hpos⟩
  let xn : ball x.val r := ⟨x.val + (-t) • v, hneg⟩
  let xc : ball x.val r := ⟨x.val, mem_ball_self hr⟩
  have hmatch : plLocalSign h hh (j xp) = plLocalSign g hg (k xp) := by
    apply plLocalSign_eq_of_eqOn h g hh hg (j xp).property (k xp).property
      (isOpen_lt continuous_const ell.continuous)
      (show 0 < ell (x.val + t • v) by rw [hheight]; exact ht)
    intro y hy
    rw [hgmap, if_pos (le_of_lt hy)]
  have hidentity : plLocalSign g hg (k xn) = 1 := by
    have heq := plLocalSign_eq_of_eqOn g (OpenPartialHomeomorph.refl E)
      hg (piecewiseAffineGroupoid E).id_mem (k xn).property (mem_univ _)
      (isOpen_lt ell.continuous continuous_const)
      (show ell (x.val + (-t) • v) < 0 by rw [hheight]; exact neg_neg_of_pos ht)
      (fun y hy => by rw [hgmap, if_neg (not_le.mpr hy)]; rfl)
    exact heq.trans (plLocalSign_refl _)
  exact (hhs.apply_eq_of_preconnectedSpace xc xp).trans
    (hmatch.trans ((hgg.apply_eq_of_preconnectedSpace xp xn).trans hidentity))

end Geometry
