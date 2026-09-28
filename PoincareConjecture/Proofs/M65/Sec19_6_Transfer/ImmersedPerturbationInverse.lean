import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationSard











set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M65Perturbation

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]



def augmentedDerivative (A : ((E × P) × E) →L[ℝ] E) :
    ((E × P) × E) →L[ℝ] E × (P × E) :=
  A.prod (((ContinuousLinearMap.snd ℝ E P).comp
    (ContinuousLinearMap.fst ℝ (E × P) E)).prod (ContinuousLinearMap.snd ℝ (E × P) E))




theorem augmentedDerivative_bijective (A : ((E × P) × E) →L[ℝ] E)
    (hA : Function.Bijective (fun u : E => A ((u, 0), 0))) :
    Function.Bijective (augmentedDerivative A) := by
  have hsplit (u : E) (v : P) (z : E) :
      A ((u, v), z) = A ((u, 0), 0) + A ((0, v), z) := by
    rw [← map_add]
    congr 1
    simp
  constructor
  · rintro ⟨⟨u, v⟩, z⟩ ⟨⟨u', v'⟩, z'⟩ h
    have hv : v = v' := congrArg (fun w : E × (P × E) => w.2.1) h
    have hz : z = z' := congrArg (fun w : E × (P × E) => w.2.2) h
    subst v'
    subst z'
    have hfirst : A ((u, v), z) = A ((u', v), z) := congrArg Prod.fst h
    rw [hsplit u v z, hsplit u' v z] at hfirst
    have hu : u = u' := hA.1 (add_right_cancel hfirst)
    subst u'
    rfl
  · rintro ⟨q, v, z⟩
    obtain ⟨u, hu⟩ := hA.2 (q - A ((0, v), z))
    change A ((u, 0), 0) = q - A ((0, v), z) at hu
    refine ⟨((u, v), z), ?_⟩
    change (A ((u, v), z), v, z) = (q, v, z)
    rw [hsplit, hu, sub_add_cancel]

variable [CompleteSpace E] [CompleteSpace P]





theorem exists_augmented_inverse (Q : ((E × P) × E) → E) (w : (E × P) × E)
    (hQ : ContDiffAt ℝ 1 Q w)
    (hblock : Function.Bijective (fun u : E => fderiv ℝ Q w ((u, 0), 0))) :
    ∃ e : OpenPartialHomeomorph ((E × P) × E) (E × (P × E)),
      w ∈ e.source ∧
      (∀ v, e v = (Q v, v.1.2, v.2)) ∧
      ContDiffAt ℝ 1 (e.symm : (E × (P × E)) → ((E × P) × E)) (e w) := by
  let f : ((E × P) × E) → E × (P × E) := fun v => (Q v, v.1.2, v.2)
  have hf : ContDiffAt ℝ 1 f w := hQ.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd)
  have hid := hasFDerivAt_id (𝕜 := ℝ) w
  have htail := hid.fst.snd.prodMk hid.snd
  have hraw := hQ.differentiableAt_one.hasFDerivAt.prodMk htail
  have hD : HasFDerivAt f (augmentedDerivative (fderiv ℝ Q w)) w := by
    simpa +instances only [f, augmentedDerivative, ContinuousLinearMap.comp_id, id_eq] using! hraw
  have hbij := augmentedDerivative_bijective (fderiv ℝ Q w) hblock
  let A : ((E × P) × E) ≃L[ℝ] E × (P × E) :=
    ContinuousLinearEquiv.ofBijective (augmentedDerivative (fderiv ℝ Q w))
      (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  have hA : HasFDerivAt f (A : ((E × P) × E) →L[ℝ] E × (P × E)) w := by
    rw [show (A : ((E × P) × E) →L[ℝ] E × (P × E)) =
      augmentedDerivative (fderiv ℝ Q w) from ContinuousLinearEquiv.coe_ofBijective _ _ _]
    exact hD
  refine ⟨hf.toOpenPartialHomeomorph f hA one_ne_zero,
    hf.mem_toOpenPartialHomeomorph_source hA one_ne_zero, fun _ => rfl, ?_⟩
  exact hf.to_localInverse hA one_ne_zero

end PoincareConjecture.M65Perturbation
