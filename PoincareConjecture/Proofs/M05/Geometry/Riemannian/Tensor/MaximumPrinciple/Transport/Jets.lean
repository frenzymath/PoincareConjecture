
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Coordinates
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Chart
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Local









noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma mem_tangentTrivialization_of_mem_extChartAt {p x : M}
    (hx : x ∈ (extChartAt (𝓡 n) p).source) :
    x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).baseSet := by
  simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source] using hx


def centeredChartDomain (p : M) : Set (EuclideanSpace ℝ (Fin n)) :=
  {z | extChartAt (𝓡 n) p p + z ∈ (extChartAt (𝓡 n) p).target}

omit [IsManifold (𝓡 n) ∞ M] in
lemma isOpen_centeredChartDomain (p : M) : IsOpen (centeredChartDomain (n := n) p) :=
  (isOpen_extChartAt_target (I := 𝓡 n) p).preimage (continuous_const.add continuous_id)

omit [IsManifold (𝓡 n) ∞ M] in
lemma zero_mem_centeredChartDomain (p : M) : (0 : EuclideanSpace ℝ (Fin n)) ∈ centeredChartDomain p := by
  simpa only [centeredChartDomain, mem_ofPred_eq, add_zero] using
    (extChartAt (𝓡 n) p).map_source (mem_extChartAt_source p)


def centeredConnectionCoefficient (D : LeviCivitaData g) (p : M)
    (z : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) :=
  D.coordinateConnectionCoefficient p
    ((extChartAt (𝓡 n) p).symm (extChartAt (𝓡 n) p p + z))

lemma contDiffOn_centeredConnectionCoefficient (D : LeviCivitaData g) (p : M) :
    ContDiffOn ℝ ∞ (D.centeredConnectionCoefficient p) (centeredChartDomain p) := by
  intro z hz
  have hsymm : ContMDiffAt (𝓡 n) (𝓡 n) ∞
      (extChartAt (𝓡 n) p).symm (extChartAt (𝓡 n) p p + z) :=
    (contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds hz)
  have hx := mem_tangentTrivialization_of_mem_extChartAt ((extChartAt (𝓡 n) p).map_target hz)
  have hcoeff := D.contMDiffAt_coordinateConnectionCoefficient p hx
  have htrans : ContMDiffAt (𝓡 n) (𝓡 n) ∞
      (fun w : EuclideanSpace ℝ (Fin n) => extChartAt (𝓡 n) p p + w) z :=
    contMDiffAt_const.add contMDiffAt_id
  have h := hcoeff.comp z (hsymm.comp z htrans)
  exact (contMDiffAt_iff_contDiffAt.mp h).contDiffWithinAt


def fieldFromCenteredCoordinates (p : M)
    (Y : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : M) : TangentSpace (𝓡 n) x :=
  constantCoordinateField p (Y (extChartAt (𝓡 n) p x - extChartAt (𝓡 n) p p)) x

lemma coordinateRepresentative_fieldFromCenteredCoordinates (p : M)
    (Y : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) {x : M}
    (hx : x ∈ (extChartAt (𝓡 n) p).source) :
    coordinateRepresentative p (fieldFromCenteredCoordinates p Y) x =
      Y (extChartAt (𝓡 n) p x - extChartAt (𝓡 n) p p) := by
  exact Trivialization.continuousLinearMapAt_symmL (R := ℝ) _
    (mem_tangentTrivialization_of_mem_extChartAt hx) _

lemma contMDiffAt_fieldFromCenteredCoordinates (p : M)
    {Y : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {x : M}
    (hY : ContDiffAt ℝ ∞ Y (extChartAt (𝓡 n) p x - extChartAt (𝓡 n) p p))
    (hx : x ∈ (extChartAt (𝓡 n) p).source) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (fieldFromCenteredCoordinates p Y)) x := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n)) p
  have hchart := contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞) (x := p)
    (show x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source by
      simpa only [extChartAt_source] using hx)
  have hYc : ContMDiffAt (𝓡 n) (𝓡 n) ∞
      (fun y => Y (extChartAt (𝓡 n) p y - extChartAt (𝓡 n) p p)) x :=
    (contMDiffAt_iff_contDiffAt.mpr hY).comp x (hchart.sub contMDiffAt_const)
  have hv : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y => TotalSpace.mk' E y (Y (extChartAt (𝓡 n) p y - extChartAt (𝓡 n) p p))) x := by
    rw [contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using hYc⟩
  exact (e.contMDiffAt_symmL (IB := 𝓡 n) (n := ∞)
    (mem_tangentTrivialization_of_mem_extChartAt hx)).clm_bundle_apply hv



lemma coordinate_connection_fieldFromCenteredCoordinates (D : LeviCivitaData g) (p : M)
    {Y : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {x : M}
    (hY : ContDiffAt ℝ ∞ Y (extChartAt (𝓡 n) p x - extChartAt (𝓡 n) p p))
    (hx : x ∈ (extChartAt (𝓡 n) p).source) (u : TangentSpace (𝓡 n) x) :
    (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).continuousLinearMapAt
      ℝ x (D.connection (fieldFromCenteredCoordinates p Y) x u) =
      Poincare.Riemannian.RadialTransport.covariantDerivative
        (D.centeredConnectionCoefficient p) Y
        (extChartAt (𝓡 n) p x - extChartAt (𝓡 n) p p)
        ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).continuousLinearMapAt
          ℝ x u) := by
  let c := extChartAt (𝓡 n) p
  have hx' := mem_tangentTrivialization_of_mem_extChartAt hx
  have hZ := (contMDiffAt_fieldFromCenteredCoordinates p hY hx).mdifferentiableAt (by simp)
  have hrep : (coordinateRepresentative p (fieldFromCenteredCoordinates p Y) ∘ c.symm)
      =ᶠ[𝓝 (c x)] (fun z => Y (z - c p)) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds (c.map_source hx)]
      with z hz
    change coordinateRepresentative p (fieldFromCenteredCoordinates p Y) (c.symm z) = _
    rw [coordinateRepresentative_fieldFromCenteredCoordinates p Y (c.map_target hz)]
    change Y (c (c.symm z) - c p) = _
    rw [c.right_inv hz]
  have hder : fderiv ℝ (fun z => Y (z - c p)) (c x) = fderiv ℝ Y (c x - c p) := by
    have h := (hY.differentiableAt (by simp)).hasFDerivAt.comp (c x)
      ((hasFDerivAt_id (c x)).sub_const (c p))
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using h.fderiv
  rw [D.coordinate_connection_eq p hx' hZ u,
    coordinateRepresentative_mvfderiv_eq_fderiv p hx' hZ u,
    hrep.fderiv_eq, hder,
    coordinateRepresentative_fieldFromCenteredCoordinates p Y hx]
  unfold Poincare.Riemannian.RadialTransport.covariantDerivative centeredConnectionCoefficient
  have hcenter : c p + (c x - c p) = c x := by abel
  rw [show extChartAt (𝓡 n) p p +
    (extChartAt (𝓡 n) p x - extChartAt (𝓡 n) p p) = c x from hcenter, c.left_inv hx]

lemma coordinateRepresentative_extend (p : M) (a : TangentSpace (𝓡 n) p) {x : M}
    (hx : x ∈ (extChartAt (𝓡 n) p).source) :
    coordinateRepresentative p (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a) x =
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).continuousLinearMapAt
        ℝ p a := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  have hx' := mem_tangentTrivialization_of_mem_extChartAt hx
  have hp := FiberBundle.mem_baseSet_trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n)) p
  change e.continuousLinearMapAt ℝ x (e.symm x (e ⟨p, a⟩).2) = _
  rw [← e.symmL_apply (R := ℝ) hx', e.continuousLinearMapAt_symmL (R := ℝ) hx']
  exact (e.continuousLinearMapAt_apply_of_mem ℝ hp a).symm

lemma connection_fieldFromCenteredCoordinates_zero (D : LeviCivitaData g) (p : M)
    {Y : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hY : ContDiff ℝ ∞ Y)
    (hfirst : ∀ u, Poincare.Riemannian.RadialTransport.covariantDerivative
      (D.centeredConnectionCoefficient p) Y 0 u = 0) (a : TangentSpace (𝓡 n) p) :
    D.connection (fieldFromCenteredCoordinates p Y) p a = 0 := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  have hcoord := D.coordinate_connection_fieldFromCenteredCoordinates p
    hY.contDiffAt (mem_extChartAt_source p) a
  simp only [sub_self, hfirst] at hcoord
  have h := congrArg (e.symmL ℝ p) hcoord
  rw [e.symmL_continuousLinearMapAt (FiberBundle.mem_baseSet_trivializationAt _ _ p), map_zero] at h
  exact h

lemma second_connection_fieldFromCenteredCoordinates_zero (D : LeviCivitaData g) (p : M)
    {Y : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hY : ContDiff ℝ ∞ Y)
    (hsecond : ∀ u, Poincare.Riemannian.RadialTransport.covariantDerivative
      (D.centeredConnectionCoefficient p)
      (fun z => Poincare.Riemannian.RadialTransport.covariantDerivative
        (D.centeredConnectionCoefficient p) Y z u) 0 u = 0)
    (a : TangentSpace (𝓡 n) p) :
    D.connection (D.covariantDerivativeOnFields
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a)
      (fieldFromCenteredCoordinates p Y)) p a = 0 := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n)) p
  let u := e.continuousLinearMapAt ℝ p a
  let Γ := D.centeredConnectionCoefficient p
  let H : E → E := fun z => Poincare.Riemannian.RadialTransport.covariantDerivative Γ Y z u
  let Z := fieldFromCenteredCoordinates p Y
  let X := FiberBundle.extend E a
  have hp := mem_extChartAt_source (I := 𝓡 n) p
  have hΓ : ContDiffAt ℝ ∞ Γ 0 := (D.contDiffOn_centeredConnectionCoefficient p).contDiffAt
    ((isOpen_centeredChartDomain p).mem_nhds (zero_mem_centeredChartDomain p))
  have hH : ContDiffAt ℝ ∞ H 0 :=
    (((hY.fderiv_right (by simp)).clm_apply contDiff_const).contDiffAt).add
      ((hΓ.clm_apply contDiffAt_const).clm_apply hY.contDiffAt)
  have hZ := contMDiffAt_fieldFromCenteredCoordinates p hY.contDiffAt hp
  have hX := FiberBundle.contMDiffAt_extend (𝓡 n) E (k := ∞) a
  have hW := D.contMDiffAt_covariantDerivativeOnFields hX hZ
  have hHlift := contMDiffAt_fieldFromCenteredCoordinates p
    (by simpa only [sub_self] using hH) hp
  have heq : D.covariantDerivativeOnFields X Z =ᶠ[𝓝 p]
      fieldFromCenteredCoordinates p H := by
    filter_upwards [(extChartAt_source_mem_nhds (I := 𝓡 n) p)] with x hx
    have hx' := mem_tangentTrivialization_of_mem_extChartAt hx
    have hc := D.coordinate_connection_fieldFromCenteredCoordinates p hY.contDiffAt hx (X x)
    have hxu : e.continuousLinearMapAt ℝ x (X x) = u :=
      coordinateRepresentative_extend p a hx
    rw [hxu] at hc
    have hcoord : e.continuousLinearMapAt ℝ x (D.covariantDerivativeOnFields X Z x) =
        e.continuousLinearMapAt ℝ x (fieldFromCenteredCoordinates p H x) := by
      rw [show e.continuousLinearMapAt ℝ x (fieldFromCenteredCoordinates p H x) =
          H (extChartAt (𝓡 n) p x - extChartAt (𝓡 n) p p) from
        coordinateRepresentative_fieldFromCenteredCoordinates p H hx]
      exact hc
    have hh := congrArg (e.symmL ℝ x) hcoord
    simpa only [e.symmL_continuousLinearMapAt hx'] using hh
  have hconn := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    (hW.mdifferentiableAt (by simp)) (hHlift.mdifferentiableAt (by simp)) (by simp) heq
  change D.connection (D.covariantDerivativeOnFields X Z) p a = 0
  rw [hconn]
  have hc := D.coordinate_connection_fieldFromCenteredCoordinates p
    (by simpa only [sub_self] using hH) hp a
  simp only [sub_self] at hc
  have hz : Poincare.Riemannian.RadialTransport.covariantDerivative Γ H 0 u = 0 := hsecond u
  rw [hz] at hc
  have hh := congrArg (e.symmL ℝ p) hc
  change e.symmL ℝ p (e.continuousLinearMapAt ℝ p
    (D.connection (fieldFromCenteredCoordinates p H) p a)) = e.symmL ℝ p 0 at hh
  rw [e.symmL_continuousLinearMapAt (FiberBundle.mem_baseSet_trivializationAt _ _ p), map_zero] at hh
  exact hh




theorem exists_radialParallelField (D : LeviCivitaData g) (p : M)
    (v : TangentSpace (𝓡 n) p) :
    ∃ (r : ℝ) (Y : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      0 < r ∧ Metric.ball 0 r ⊆ centeredChartDomain (n := n) p ∧ ContDiff ℝ ∞ Y ∧
      fieldFromCenteredCoordinates p Y p = v ∧
      (∀ u ∈ Metric.ball 0 r, ∀ t ∈ Icc (-1 : ℝ) 1,
        HasDerivAt (fun s : ℝ => Y (s • u))
          (-(D.centeredConnectionCoefficient p (t • u) u (Y (t • u)))) t) ∧
      (∀ a, D.connection (fieldFromCenteredCoordinates p Y) p a = 0) ∧
      (∀ a, D.connection (D.covariantDerivativeOnFields
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a)
        (fieldFromCenteredCoordinates p Y)) p a = 0) := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  obtain ⟨r, Y, hr, hrU, hY, hY0, hpar, hfirst, hsecond⟩ :=
    Poincare.Riemannian.RadialTransport.exists_field_local
      (isOpen_centeredChartDomain p) (zero_mem_centeredChartDomain p)
      (D.contDiffOn_centeredConnectionCoefficient p) (e.continuousLinearMapAt ℝ p v)
  refine ⟨r, Y, hr, hrU, hY, ?_, hpar,
    D.connection_fieldFromCenteredCoordinates_zero p hY hfirst,
    D.second_connection_fieldFromCenteredCoordinates_zero p hY hsecond⟩
  change e.symmL ℝ p (Y (extChartAt (𝓡 n) p p - extChartAt (𝓡 n) p p)) = v
  rw [sub_self, hY0, e.symmL_continuousLinearMapAt (FiberBundle.mem_baseSet_trivializationAt _ _ p)]

end PoincareConjecture.LeviCivitaData
