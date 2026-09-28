import PoincareConjecture.Proofs.M76.PrimeReduction.ReturningFaceCoordinates
import Mathlib.Analysis.Normed.Affine.AddTorsorBases










set_option autoImplicit false

open Set Module

namespace ContinuousAffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem exists_normal_extension (F : (ℝ × ℝ) →ᴬ[ℝ] E)
    (hi : Function.Injective F) (h3 : Module.finrank ℝ E = 3) :
    ∃ T : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E,
      (∀ z : ℝ × ℝ, T (z, 0) = F z) ∧
      (∀ z : ℝ × ℝ, T.symm (F z) = (z, 0)) ∧
      ∀ x : E, x ∈ range F ↔ (T.symm x).2 = 0 := by
  classical
  let L := F.toAffineMap.linear
  have hLi : Function.Injective L := F.toAffineMap.linear_injective_iff.mpr hi
  have hproper : L.range ≠ ⊤ := by
    intro htop
    have hrank := LinearMap.finrank_range_of_inj hLi
    rw [htop, finrank_top, h3] at hrank
    norm_num [Module.finrank_prod] at hrank
  have hex : ¬ ∀ n : E, n ∈ L.range := by
    intro h
    apply hproper
    exact top_unique (fun x _ => h x)
  obtain ⟨n, hn⟩ := not_forall.mp hex
  let g : ((ℝ × ℝ) × ℝ) →ᵃ[ℝ] E :=
    F.toAffineMap.comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ).toAffineMap +
      ((LinearMap.snd ℝ (ℝ × ℝ) ℝ).smulRight n).toAffineMap
  have hg (z : (ℝ × ℝ) × ℝ) : g z = F z.1 + z.2 • n := rfl
  have hgi : Function.Injective g := by
    intro p q hpq
    rw [hg, hg] at hpq
    have ht : p.2 = q.2 := by
      by_contra hne
      have hdiff : F p.1 - F q.1 ∈ L.range :=
        ⟨p.1 - q.1, F.toAffineMap.linearMap_vsub p.1 q.1⟩
      have heq : F p.1 - F q.1 = (q.2 - p.2) • n := by
        rw [sub_smul, sub_eq_sub_iff_add_eq_add]
        simpa only [add_comm (q.2 • n) (F q.1)] using hpq
      exact hn ((L.range.smul_mem_iff (sub_ne_zero.mpr (Ne.symm hne))).mp (heq ▸ hdiff))
    exact Prod.ext (hi (add_right_cancel (ht ▸ hpq))) ht
  have hgli : Function.Injective g.linear := g.linear_injective_iff.mpr hgi
  have hgrange : g.linear.range = ⊤ := Submodule.eq_top_of_finrank_eq (by
    rw [LinearMap.finrank_range_of_inj hgli, h3]
    norm_num [Module.finrank_prod])
  have hgs : Function.Surjective g :=
    g.linear_surjective_iff.mp (LinearMap.range_eq_top.mp hgrange)
  let T := (AffineEquiv.ofBijective ⟨hgi, hgs⟩).toContinuousAffineEquiv
  have hzero (z : ℝ × ℝ) : T (z, 0) = F z := by
    change F z + (0 : ℝ) • n = F z
    rw [zero_smul, add_zero]
  have hinverse (z : ℝ × ℝ) : T.symm (F z) = (z, 0) := by
    rw [← hzero z, T.symm_apply_apply]
  refine ⟨T, hzero, hinverse, ?_⟩
  intro x
  constructor
  · rintro ⟨z, rfl⟩
    rw [hinverse]
  · intro hx
    refine ⟨(T.symm x).1, ?_⟩
    rw [← hzero]
    have hz : ((T.symm x).1, 0) = T.symm x := Prod.ext rfl hx.symm
    rw [hz, T.apply_symm_apply]

end ContinuousAffineMap
