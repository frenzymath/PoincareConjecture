import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.OrthogonalKernelProjection

/-!
# Recovering normalized projections from their kernels

For a fixed frame inclusion, the normalized projection is recovered
continuously from the orthogonal projector onto its kernel. This is
the inverse coordinate calculation in Cairns 1940, Lemma 5.1, p. 801;
see M76 derivation 28. No orthonormality of the fixed frame is assumed.
-/

set_option autoImplicit false

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The Gram operator of an injective frame is invertible.
See Cairns p. 801 and M76 derivation 28. -/
theorem isInvertible_adjoint_comp_self_of_injective (J : F →L[ℝ] E)
    (hJ : Function.Injective J) : ((adjoint J).comp J).IsInvertible := by
  have hker : ((adjoint J).comp J).ker = ⊥ := by
    rw [ker_adjoint_comp_self, LinearMap.ker_eq_bot.mpr hJ]
  have hinj : Function.Injective ((adjoint J).comp J) := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective ((adjoint J).comp J) :=
    LinearMap.injective_iff_surjective.mp hinj
  exact ⟨ContinuousLinearEquiv.ofBijective ((adjoint J).comp J) hker
    (LinearMap.range_eq_top.mpr hsurj), rfl⟩

/-- The frame followed by orthogonal projection away from a proposed
kernel. See Cairns p. 801 and M76 derivation 28. -/
def perpendicularFrame (J : F →L[ℝ] E) (P : E →L[ℝ] E) : F →L[ℝ] E :=
  (ContinuousLinearMap.id ℝ E - P).comp J

/-- The normalized projection formula associated with a kernel
projector. It has geometric meaning when the perpendicular frame is
injective. See Cairns p. 801 and M76 derivation 28. -/
noncomputable def frameProjectionFormula (J : F →L[ℝ] E) (P : E →L[ℝ] E) : E →L[ℝ] F :=
  (((adjoint (perpendicularFrame J P)).comp (perpendicularFrame J P)).inverse.comp
    (adjoint (perpendicularFrame J P))).comp (ContinuousLinearMap.id ℝ E - P)

omit [FiniteDimensional ℝ F] in
/-- A right inverse remains injective after orthogonal projection
away from the corresponding kernel.
See Cairns p. 801 and M76 derivation 28. -/
theorem injective_perpendicularFrame_of_rightInverse (Q : E →L[ℝ] F) (J : F →L[ℝ] E)
    (hJ : Function.RightInverse J Q) :
    Function.Injective (perpendicularFrame J Q.ker.starProjection) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  change J x - Q.ker.starProjection (J x) = 0 at hx
  have hmem : J x ∈ Q.ker := by
    rw [sub_eq_zero.mp hx]
    exact Q.ker.starProjection_apply_mem _
  have he : Q (J x) = 0 := hmem
  simpa only [hJ x] using he

/-- Recover a normalized projection from its geometric kernel
projector. The frame need not be orthonormal.
See Cairns p. 801 and M76 derivation 28. -/
theorem frameProjectionFormula_ker (Q : E →L[ℝ] F) (J : F →L[ℝ] E)
    (hJ : Function.RightInverse J Q) :
    frameProjectionFormula J Q.ker.starProjection = Q := by
  let P := Q.ker.starProjection
  let A := perpendicularFrame J P
  have hA : Function.Injective A := Q.injective_perpendicularFrame_of_rightInverse J hJ
  have hG := A.isInvertible_adjoint_comp_self_of_injective hA
  ext x
  have hmem : x - J (Q x) ∈ Q.ker := by
    change Q (x - J (Q x)) = 0
    rw [map_sub, hJ, sub_self]
  have hzero : (ContinuousLinearMap.id ℝ E - P) (x - J (Q x)) = 0 := by
    change (x - J (Q x)) - Q.ker.starProjection (x - J (Q x)) = 0
    rw [Q.ker.starProjection_eq_self_iff.mpr hmem, sub_self]
  have he : (ContinuousLinearMap.id ℝ E - P) x = A (Q x) := by
    change (ContinuousLinearMap.id ℝ E - P) x =
      (ContinuousLinearMap.id ℝ E - P) (J (Q x))
    exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)
  change ((adjoint A).comp A).inverse ((adjoint A) ((ContinuousLinearMap.id ℝ E - P) x)) = Q x
  rw [he]
  exact hG.inverse_apply_self (Q x)

/-- The inverse formula varies continuously wherever the projected
frame is independent. See Cairns p. 801 and M76 derivation 28. -/
theorem continuousAt_frameProjectionFormula (J : F →L[ℝ] E) (P : E →L[ℝ] E)
    (hP : Function.Injective (perpendicularFrame J P)) :
    ContinuousAt (frameProjectionFormula J) P := by
  have hD : ContinuousAt (fun R : E →L[ℝ] E => ContinuousLinearMap.id ℝ E - R) P :=
    continuousAt_const.sub continuousAt_id
  have hA : ContinuousAt (perpendicularFrame J) P := hD.clm_comp continuousAt_const
  have hAdj : ContinuousAt (fun R => adjoint (perpendicularFrame J R)) P :=
    adjoint.continuous.continuousAt.comp hA
  have hG : ContinuousAt (fun R => (adjoint (perpendicularFrame J R)).comp
      (perpendicularFrame J R)) P := hAdj.clm_comp hA
  have hinverse : ContinuousAt (inverse : (F →L[ℝ] F) → F →L[ℝ] F)
      ((adjoint (perpendicularFrame J P)).comp (perpendicularFrame J P)) := by
    have hInv := (perpendicularFrame J P).isInvertible_adjoint_comp_self_of_injective hP
    exact (hInv.contDiffAt_map_inverse (n := 0)).continuousAt
  have hi : ContinuousAt (fun R => ((adjoint (perpendicularFrame J R)).comp
      (perpendicularFrame J R)).inverse) P :=
    hinverse.comp (f := fun R => (adjoint (perpendicularFrame J R)).comp
      (perpendicularFrame J R)) hG
  exact (hi.clm_comp hAdj).clm_comp hD

end ContinuousLinearMap
