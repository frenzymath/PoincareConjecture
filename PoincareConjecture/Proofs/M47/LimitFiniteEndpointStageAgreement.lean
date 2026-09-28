import PoincareConjecture.Proofs.M47.LimitFiniteEndpointCompatibility
import PoincareConjecture.Proofs.M47.LimitFiniteEndpointChartMaps









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance finiteStageAgreementDualAdd :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteStageAgreementDualSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance finiteStageAgreementBilinAdd :
    NormedAddCommGroup Bilin := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteStageAgreementBilinSpace :
    NormedSpace ℝ Bilin := ContinuousLinearMap.toNormedSpace



theorem limitFinite_endpoint_clocked_compatibility
    (F : ℕ → SurgeryFlowData.{u}) (C : GeneralizedSliceCarrier.{u})
    (index : ℕ → ℕ) (origin Q b c : ℕ → ℝ) (U W : TopologicalSpace.Opens C.carrier)
    (e : ∀ k, SurgeryFlowCylinder (F (index k)) C (origin (index k)) (Q (index k))
      (Icc (b k) 0) U)
    (f : ∀ k, SurgeryFlowCylinder (F (index k)) C (origin (index k)) (Q (index k))
      (Icc (c k) 0) W)
    {t : ℝ} (ht : t ≤ 0) (htime : ∀ᶠ k in atTop, b k ≤ t ∧ c k ≤ t)
    (hzero : ∀ᶠ k in atTop,
      ∀ he0 : 0 ∈ Icc (b k) 0, ∀ hf0 : 0 ∈ Icc (c k) 0,
        ∀ x ∈ (U : Set C.carrier) ∩ W, (e k).forward 0 he0 x = (f k).forward 0 hf0 x)
    {I J : Set ℝ} (A : ℕ → RicciFlow 3 U I) (D : ℕ → RicciFlow 3 W J)
    (hA : ∀ᶠ k in atTop, ∀ htk : t ∈ Icc (b k) 0,
      ∀ (x : U) (v w : E), ((A k).metric t).inner x v w = (e k).pullbackInner t htk x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w))
    (hD : ∀ᶠ k in atTop, ∀ htk : t ∈ Icc (c k) 0,
      ∀ (x : W) (v w : E), ((D k).metric t).inner x v w = (f k).pullbackInner t htk x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : W → C.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : W → C.carrier) x w))
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞)
    (Ψ : PartialDiffeomorph (𝓡 3) (𝓡 3) E W ∞) (z w : E)
    (hpoint : (Φ z).val = (Ψ w).val) (v1 u1 v2 u2 : E)
    (hv : mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (Φ z)
        (mfderiv (𝓡 3) (𝓡 3) Φ z v1) =
      mfderiv (𝓡 3) (𝓡 3) (Subtype.val : W → C.carrier) (Ψ w)
        (mfderiv (𝓡 3) (𝓡 3) Ψ w v2))
    (hu : mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (Φ z)
        (mfderiv (𝓡 3) (𝓡 3) Φ z u1) =
      mfderiv (𝓡 3) (𝓡 3) (Subtype.val : W → C.carrier) (Ψ w)
        (mfderiv (𝓡 3) (𝓡 3) Ψ w u2))
    (c1 c2 : ℝ) (B1 B2 : ℝ × E → Bilin)
    (hconv1 : ∀ v u, Tendsto (fun k =>
      ((A k).metric ((t - c1) + c1)).pullbackCoefficients Φ z v u)
        atTop (𝓝 (B1 (t - c1, z) v u)))
    (hconv2 : ∀ v u, Tendsto (fun k =>
      ((D k).metric ((t - c2) + c2)).pullbackCoefficients Ψ w v u)
        atTop (𝓝 (B2 (t - c2, w) v u))) :
    B1 (t - c1, z) v1 u1 = B2 (t - c2, w) v2 u2 := by
  apply limitFinite_endpoint_physical_compatibility (fun k => F (index k)) C
    (fun k => origin (index k)) (fun k => Q (index k)) b c U W e f ht htime hzero
    (fun k => (A k).metric t) (fun k => (D k).metric t) hA hD
    Φ Ψ z w hpoint v1 u1 v2 u2 hv hu (B1 (t - c1, z)) (B2 (t - c2, w))
  · intro v u
    simpa only [sub_add_cancel] using hconv1 v u
  · intro v u
    simpa only [sub_add_cancel] using hconv2 v u



theorem limitFinite_endpoint_stage_agreement
    {n : ℕ} {ι κ : Type*} {P : ι → Type*} {Q : κ → Type*} {M : Type*}
    [∀ i, TopologicalSpace (P i)] [∀ j, TopologicalSpace (Q j)] [TopologicalSpace M]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Q j)]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [∀ i, IsManifold (𝓡 n) ∞ (P i)] [∀ j, IsManifold (𝓡 n) ∞ (Q j)]
    [IsManifold (𝓡 n) ∞ M]
    (V W : TopologicalSpace.Opens M) (q : ∀ i, P i → M) (r : ∀ j, Q j → M)
    (hq : ∀ i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (q i))
    (hr : ∀ j, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (r j))
    (hcoverV : ∀ y ∈ V, ∃ i x, q i x = y)
    (hcoverW : ∀ y ∈ W, ∃ j x, r j x = y)
    (g : ∀ i, RiemannianMetric n (P i)) (h : ∀ j, RiemannianMetric n (Q j))
    (gV : RiemannianMetric n V) (gW : RiemannianMetric n W)
    (hV : ∀ i (x : P i) (hx : q i x ∈ V) (a b : TangentSpace (𝓡 n) x),
      (g i).inner x a b = gV.inner ⟨q i x, hx⟩
        (mfderiv (𝓡 n) (𝓡 n) (q i) x a) (mfderiv (𝓡 n) (𝓡 n) (q i) x b))
    (hW : ∀ j (x : Q j) (hx : r j x ∈ W) (a b : TangentSpace (𝓡 n) x),
      (h j).inner x a b = gW.inner ⟨r j x, hx⟩
        (mfderiv (𝓡 n) (𝓡 n) (r j) x a) (mfderiv (𝓡 n) (𝓡 n) (r j) x b))
    (hpair : ∀ i j (x : P i) (y : Q j), q i x = r j y →
      ∀ (a b : TangentSpace (𝓡 n) x) (c d : TangentSpace (𝓡 n) y),
        mfderiv (𝓡 n) (𝓡 n) (q i) x a = mfderiv (𝓡 n) (𝓡 n) (r j) y c →
        mfderiv (𝓡 n) (𝓡 n) (q i) x b = mfderiv (𝓡 n) (𝓡 n) (r j) y d →
        (g i).inner x a b = (h j).inner y c d)
    (y : M) (hyV : y ∈ V) (hyW : y ∈ W) (v w : EuclideanSpace ℝ (Fin n)) :
    gV.inner ⟨y, hyV⟩ v w = gW.inner ⟨y, hyW⟩ v w := by
  obtain ⟨i, x, hx⟩ := hcoverV y hyV
  obtain ⟨j, z, hz⟩ := hcoverW y hyW
  have hxV : q i x ∈ V := (congrArg (fun p => p ∈ V) hx).mpr hyV
  have hzW : r j z ∈ W := (congrArg (fun p => p ∈ W) hz).mpr hyW
  let L := (hq i).mfderivToContinuousLinearEquiv (by simp) x
  let K := (hr j).mfderivToContinuousLinearEquiv (by simp) z
  have hLv : mfderiv (𝓡 n) (𝓡 n) (q i) x (L.symm v) = v := L.apply_symm_apply _
  have hLw : mfderiv (𝓡 n) (𝓡 n) (q i) x (L.symm w) = w := L.apply_symm_apply _
  have hKv : mfderiv (𝓡 n) (𝓡 n) (r j) z (K.symm v) = v := K.apply_symm_apply _
  have hKw : mfderiv (𝓡 n) (𝓡 n) (r j) z (K.symm w) = w := K.apply_symm_apply _
  have hleft := hV i x hxV (L.symm v) (L.symm w)
  have hright := hW j z hzW (K.symm v) (K.symm w)
  rw [hLv, hLw] at hleft
  rw [hKv, hKw] at hright
  have hxy := hpair i j x z (hx.trans hz.symm) (L.symm v) (L.symm w)
    (K.symm v) (K.symm w) (hLv.trans hKv.symm) (hLw.trans hKw.symm)
  have heq := hleft.symm.trans (hxy.trans hright)
  have hvpoint : (⟨q i x, hxV⟩ : V) = ⟨y, hyV⟩ := Subtype.ext hx
  have hwpoint : (⟨r j z, hzW⟩ : W) = ⟨y, hyW⟩ := Subtype.ext hz
  exact (congrArg (fun p : V => gV.inner p v w) hvpoint).symm.trans
    (heq.trans (congrArg (fun p : W => gW.inner p v w) hwpoint))

end PoincareConjecture.M47
