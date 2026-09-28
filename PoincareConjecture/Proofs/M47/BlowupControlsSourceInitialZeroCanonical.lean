import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialOlderOrdinary
import PoincareConjecture.Proofs.M47.CanonicalNeckCylinderMetric
import PoincareConjecture.Proofs.M47.CanonicalNeckPhysicalAssembly











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47



theorem source_initial_zero_age_canonical
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {g : RiemannianMetric 3 C.carrier} (N : EpsilonNeck g)
    {T q k tau epsilon Cc : ℝ} (hk : 0 < k) (htau : 0 < tau)
    (hepsilon : N.epsilon ≤ epsilon) (hepsilonSmall : epsilon < 1 / 2)
    (hscale : N.scale⁻¹ ^ 2 = q * k)
    (hclock : MapsTo (fun u : ℝ => u / k) (Icc (-1 : ℝ) 0) (Icc (-tau) 0))
    (old : SurgeryFlowCylinder F C T q (Icc (-tau) 0) N.carrier)
    (hfamily : RoundCylinderFamilyClose N.epsilon (Icc (-1 : ℝ) 0)
      (fun u z v w => k * surgeryCylinderPullback old N.coordinate_map (u / k) z v w))
    (D : PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier (F.slice T).carrier ∞)
    (hsource : D.source = N.carrier)
    (hzero : ∀ x, HEq (old.forward 0 ⟨by linarith only [htau], le_rfl⟩ x) (D x))
    (hmetric : ∀ x ∈ D.source, ∀ v w : TangentSpace (𝓡 3) x,
      (F.metric T).inner (D x) (mfderiv (𝓡 3) (𝓡 3) D x v)
        (mfderiv (𝓡 3) (𝓡 3) D x w) = g.inner x v w) :
    SurgeryCanonicalControl F T (D N.center) epsilon Cc := by
  let E := N.restrict hepsilon hepsilonSmall
  have hq : 0 < q := old.scale_pos
  have hQ : 0 < E.scale⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr E.scale_pos)
  let phi := fun u : ℝ => u / k
  have hmem : MapsTo phi (Ioc (-1 : ℝ) 0) (Icc (-tau) 0) :=
    fun _ hu => hclock ⟨hu.1.le, hu.2⟩
  have hmono : StrictMonoOn phi (Ioc (-1 : ℝ) 0) := by
    intro u _ v _ huv
    exact (div_lt_div_iff_of_pos_right hk).mpr huv
  have hphysical : ∀ u ∈ Ioc (-1 : ℝ) 0,
      T + u / (E.scale⁻¹ ^ 2) = T + phi u / q := by
    intro u _
    change T + u / (N.scale⁻¹ ^ 2) = T + (u / k) / q
    rw [hscale]
    field_simp
  let raw := seedCylinderReclock old hQ ordConnected_Ioc phi hmem hmono hphysical
  let e := raw.restrict Subset.rfl ordConnected_Ioc
    (show E.carrier ⊆ N.carrier from inter_subset_left)
  have hratio : (E.scale⁻¹ ^ 2) / q = k := by
    change (N.scale⁻¹ ^ 2) / q = k
    rw [hscale, mul_div_cancel_left₀ k hq.ne']
  have hrecent : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun u z v w => k * surgeryCylinderPullback old N.coordinate_map (u / k) z v w) := by
    obtain ⟨hs, b, hb, hbound⟩ := hfamily
    exact ⟨fun u hu => hs u ⟨hu.1.le, hu.2⟩, b, hb,
      fun u hu => hbound u ⟨hu.1.le, hu.2⟩⟩
  have hclose : RoundCylinderFamilyClose E.epsilon (Ioc (-1 : ℝ) 0)
      (surgeryCylinderPullback e E.coordinate_map) := by
    have hshort := hrecent.mono_epsilon N.epsilon_pos hepsilon
      (fun _ hu => hu.2.trans_lt zero_lt_one)
    apply hshort.congr_cylinder
    intro u hu z _hz v w
    have hm := neck_reclock_cylinderPullback old hQ ordConnected_Ioc phi hmem hmono hphysical
      N.coordinate_map u hu z v w
    rw [hratio] at hm
    exact hm.symm
  have hpoint : (⟨T + 0 / (E.scale⁻¹ ^ 2), e.forward 0 (by constructor <;> norm_num) E.center⟩ :
      Σ t, (F.slice t).carrier) = ⟨T, D N.center⟩ := by
    apply Sigma.ext (by simp only [zero_div, add_zero])
    have hsame (r : ℝ) (hr : r ∈ Icc (-tau) 0) (hr0 : r = 0) :
        HEq (old.forward r hr N.center) (D N.center) := by
      subst r
      exact hzero N.center
    exact (seedCylinderReclock_forward_heq old hQ ordConnected_Ioc phi hmem hmono hphysical
      0 (by constructor <;> norm_num) N.center).trans
        (hsame _ _ (by simp only [phi, zero_div]))
  have hscalar := N.connection.scalarCurvature_eq_of_local_isometry (F.connection T)
    D.open_source D.contMDiffOn (fun x hx v w => (hmetric x hx v w).symm)
      (hsource.symm ▸ N.central_sphere_subset N.center_on_central_sphere)
  have hread := congrArg (fun p : Σ t, (F.slice t).carrier =>
    (F.connection p.1).scalarCurvature p.2) hpoint
  have hphysicalScalar : (F.connection (T + 0 / (E.scale⁻¹ ^ 2))).scalarCurvature
      (e.forward 0 (by constructor <;> norm_num) E.center) =
      E.connection.scalarCurvature E.center := hread.trans hscalar.symm
  obtain ⟨physical, hphysicalCenter⟩ :=
    exists_physical_strong_neck_of_family E e hphysicalScalar hclose
  have hcanonical : SurgeryCanonicalControl F (T + 0 / (E.scale⁻¹ ^ 2))
      (e.forward 0 (by constructor <;> norm_num) E.center) epsilon Cc :=
    SurgeryCanonicalControl.neck physical hphysicalCenter
  exact (congrArg (fun p : Σ t, (F.slice t).carrier =>
    SurgeryCanonicalControl F p.1 p.2 epsilon Cc) hpoint).mp hcanonical

end PoincareConjecture.M47
