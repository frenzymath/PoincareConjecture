import PoincareConjecture.Proofs.M04.FlowTensorRegularity
import PoincareConjecture.Proofs.M04.RiemannRegularity








set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
theorem contMDiffOn_flow_riemannEvaluation (F : RicciFlow n M J)
    {U : Set M} (hU : IsOpen U)
    (X : Fin 4 → (x : M) → TangentSpace (𝓡 n) x)
    (hX : ∀ i, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (X i)) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (F.connection p.1).riemannEvaluation p.2 (fun i ↦ X i p.2))
      (J ×ˢ U) := by
  let C (s : ℝ) (i j : Fin 4) := fun y ↦ (F.connection s).connection (X j) y (X i y)
  let P (i j k : Fin 4) : ℝ × M → ℝ := fun p ↦
    (F.metric p.1).inner p.2 (C p.1 i j p.2) (X k p.2)
  have hPair (i j k : Fin 4) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ (P i j k) (J ×ˢ U) :=
    contMDiffOn_flow_connection_pairing F hU (hX i) (hX j) (hX k)
  have hCross (i j k l : Fin 4) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M ↦ (F.metric p.1).inner p.2
          (C p.1 i j p.2) (C p.1 k l p.2)) (J ×ˢ U) := by
    let L : (p : ℝ × M) → TangentSpace (𝓡 n) p.2 →L[ℝ] ℝ :=
      fun p ↦ (F.metric p.1).inner p.2 (C p.1 i j p.2)
    apply contMDiffOn_flow_linear_connection F hU L ?_ (hX k) (hX l)
    intro V hV hVU Z hZ
    exact contMDiffOn_flow_connection_pairing F hV
      ((hX i).mono hVU) ((hX j).mono hVU) hZ
  let B := VectorField.mlieBracket (𝓡 n) (X 0) (X 1)
  have hB : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U := by
    intro y hy
    let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M := by
      apply IsManifold.of_le (n := (↑(⊤ : ℕ∞) : ℕ∞ω))
      simpa [minSmoothness_eq_infty] using
        (minSmoothness_monotone (𝕜 := ℝ)
          (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)))
    let : IsManifold (𝓡 n) (∞ + 1) M := by
      simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
    exact (((hX 0).contMDiffAt (hU.mem_nhds hy)).mlieBracket_vectorField
      (m := ⊤) (n := ⊤) ((hX 1).contMDiffAt (hU.mem_nhds hy)) (by simp)).contMDiffWithinAt
  have hCs (s : ℝ) (i j : Fin 4) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (C s i j)) U := by
    intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_section_of_metric_pairings (F.metric s) (C s i j)
    intro a
    let e := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) y
    have hye : y ∈ U ∩ e.baseSet := ⟨hy, FiberBundle.mem_baseSet_trivializationAt' y⟩
    exact (contMDiffOn_connection_pairing (F.connection s) (hU.inter e.open_baseSet)
      ((hX i).mono inter_subset_left) ((hX j).mono inter_subset_left)
      ((contMDiffOn_extend_baseSet a).mono inter_subset_right)).contMDiffAt
        ((hU.inter e.open_baseSet).mem_nhds hye)
  have hs := ((((contMDiffOn_mvfderiv_spatial hU (hPair 1 3 2) (hX 0)).sub
    (contMDiffOn_mvfderiv_spatial hU (hPair 0 3 2) (hX 1))).sub
    (hCross 1 3 0 2)).add (hCross 0 3 1 2)).sub
    (contMDiffOn_flow_connection_pairing F hU hB (hX 3) (hX 2))
  apply hs.congr
  intro p hp
  have hVd (i : Fin 4) := ((hX i).contMDiffAt (hU.mem_nhds hp.2)).mdifferentiableAt (by simp)
  have hCd (i j : Fin 4) :=
    ((hCs p.1 i j).contMDiffAt (hU.mem_nhds hp.2)).mdifferentiableAt (by simp)
  have h1 := metric_derivative_pairing (F.connection p.1) (X 0) (hCd 1 3) (hVd 2)
  have h2 := metric_derivative_pairing (F.connection p.1) (X 1) (hCd 0 3) (hVd 2)
  change (F.metric p.1).inner p.2
    ((F.connection p.1).curvature p.2 (X 0 p.2) (X 1 p.2) (X 3 p.2)) (X 2 p.2) = _
  rw [← curvatureOnFields_eq_curvature (F.connection p.1) hU (hX 0) (hX 1) (hX 3) hp.2]
  simp only [LeviCivitaData.curvatureOnFields, map_sub, sub_apply, Pi.add_apply]
  dsimp only [P, C, B] at h1 h2 ⊢
  linarith only [h1, h2]

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
theorem contDiffOn_curvatureTensor_timeSlice (F : RicciFlow n M J)
    (x : M) (u v w z : TangentSpace (𝓡 n) x) :
    ContDiffOn ℝ ∞ (fun t ↦ (F.connection t).curvatureTensor x u v w z) J := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  let U := e.baseSet
  have hx : x ∈ U := FiberBundle.mem_baseSet_trivializationAt' x
  let X : Fin 4 → (y : M) → TangentSpace (𝓡 n) y :=
    ![FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u,
      FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v,
      FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w,
      FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z]
  have hX (i : Fin 4) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (X i)) U := by
    fin_cases i
    · exact contMDiffOn_extend_baseSet u
    · exact contMDiffOn_extend_baseSet v
    · exact contMDiffOn_extend_baseSet w
    · exact contMDiffOn_extend_baseSet z
  have hslice : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun t : ℝ ↦ (t, x)) := contMDiff_id.prodMk contMDiff_const
  have hs := (contMDiffOn_flow_riemannEvaluation F e.open_baseSet X hX).comp
    hslice.contMDiffOn (show MapsTo (fun t : ℝ ↦ (t, x)) J (J ×ˢ U) from
      fun _ ht ↦ ⟨ht, hx⟩)
  have ht : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t ↦ (F.connection t).curvatureTensor x u v w z) J := by
    apply hs.congr
    intro t ht
    simp [LeviCivitaData.riemannEvaluation, X]
  exact ht.contDiffOn

end PoincareConjecture.M04

