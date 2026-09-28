import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EndPullbackFlow










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)



theorem endAxialTranslation_zero_reference {x : StandardCapSpace}
    (hx : x ∈ endReferenceRegion e) : endAxialTranslation e 0 x = x := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hh : 3 < z.2 := hz.2.1
  rw [endAxialTranslation_coordinate e 0 (by linarith)]
  simp



theorem endAxialTranslation_comp_reference (r : ℝ) (hr : -3 < r) (s : ℝ)
    {x : StandardCapSpace} (hx : x ∈ endReferenceRegion e) :
    endAxialTranslation e s (endAxialTranslation e r x) =
      endAxialTranslation e (r + s) x := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hh : 3 < z.2 := hz.2.1
  rw [endAxialTranslation_coordinate e r (by linarith),
    endAxialTranslation_coordinate e s (show 0 ≤ z.2 + r by linarith),
    endAxialTranslation_coordinate e (r + s) (by linarith)]
  simp only [add_assoc]



theorem endAxialTranslation_mfderiv_zero_reference {x : StandardCapSpace}
    (hx : x ∈ endReferenceRegion e) :
    mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e 0) x =
      ContinuousLinearMap.id ℝ StandardCapSpace := by
  have heq : endAxialTranslation e 0 =ᶠ[𝓝 x] id := by
    filter_upwards [(endReferenceRegion_isOpen e).mem_nhds hx] with y hy
    exact endAxialTranslation_zero_reference e hy
  have hh := heq.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  rw [mfderiv_id] at hh
  convert hh using 1
  rfl



theorem endAxialTranslation_mfderiv_comp_reference (r : ℝ) (hr : -3 < r)
    (s : ℝ) (hs : -3 < s) {x : StandardCapSpace}
    (hx : x ∈ endReferenceRegion e)
    (hshift : endAxialTranslation e r x ∈ endReferenceRegion e) :
    mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e (r + s)) x =
      (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e s) (endAxialTranslation e r x)).comp
        (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) x) := by
  have hd (a : ℝ) (ha : -3 < a) (y : StandardCapSpace) (hy : y ∈ endReferenceRegion e) :
      MDifferentiableAt (𝓡 3) (𝓡 3) (endAxialTranslation e a) y :=
    ((endReferenceTranslation_contMDiffOn e ha y hy).contMDiffAt
      ((endReferenceRegion_isOpen e).mem_nhds hy)).mdifferentiableAt (by simp)
  have heq : endAxialTranslation e s ∘ endAxialTranslation e r =ᶠ[𝓝 x]
      endAxialTranslation e (r + s) := by
    filter_upwards [(endReferenceRegion_isOpen e).mem_nhds hx] with y hy
    exact endAxialTranslation_comp_reference e r hr s hy
  have hh := heq.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  rw [mfderiv_comp x (hd s hs _ hshift) (hd r hr _ hx)] at hh
  exact hh.symm



theorem endAxialTranslation_inverse_mfderiv (r : ℝ) (hr : -3 < r) (hneg : -3 < -r)
    {x : StandardCapSpace} (hx : x ∈ endReferenceRegion e)
    (hshift : endAxialTranslation e r x ∈ endReferenceRegion e) :
    (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) x).inverse =
      mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e (-r)) (endAxialTranslation e r x) := by
  have hi := endReferenceTranslation_mfderiv_isInvertible e hr hx
  have hcomp := endAxialTranslation_mfderiv_comp_reference e r hr (-r) hneg hx hshift
  rw [add_neg_cancel, endAxialTranslation_mfderiv_zero_reference e hx] at hcomp
  ext v
  have hh := congrArg (fun L => L ((mfderiv (𝓡 3) (𝓡 3)
    (endAxialTranslation e r) x).inverse v)) hcomp
  change (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) x).inverse v =
    mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e (-r)) (endAxialTranslation e r x)
      (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) x
        ((mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) x).inverse v)) at hh
  rwa [hi.self_apply_inverse] at hh

end PoincareConjecture.M34
