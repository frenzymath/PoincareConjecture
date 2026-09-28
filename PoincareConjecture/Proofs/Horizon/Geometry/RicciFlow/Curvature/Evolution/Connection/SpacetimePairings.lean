import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Fields.KoszulPairing
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.Structures

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {U : Set M}

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
theorem contMDiffOn_mvfderiv_spatial
    {f : ℝ × M → ℝ} {X : (y : M) → TangentSpace (𝓡 n) y}
    (hU : IsOpen U)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (J ×ˢ U))
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p ↦ mvfderiv (𝓡 n) (fun y ↦ f (p.1, y)) p.2 (X p.2)) (J ×ˢ U) := by
  let I := 𝓘(ℝ, ℝ).prod (𝓡 n)
  let S := J ×ˢ U
  have hXP : ContMDiffOn I ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.2)) S :=
    hX.comp contMDiffOn_snd (fun _ hp ↦ hp.2)
  have hWithin : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun p ↦ mvfderivWithin (𝓡 n) (fun y ↦ f (p.1, y)) U p.2 (X p.2)) S := by
    intro p hp
    have hmap : ContMDiff (I.prod (𝓡 n)) I ∞
        (fun q : (ℝ × M) × M ↦ (q.1.1, q.2)) :=
      (contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd
    have hc : ContMDiffWithinAt (I.prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun q : (ℝ × M) × M ↦ f (q.1.1, q.2)) (S ×ˢ U) (p, p.2) :=
      (hf p hp).comp (p, p.2) (hmap (p, p.2)).contMDiffWithinAt
        (show MapsTo (fun q : (ℝ × M) × M ↦ (q.1.1, q.2)) (S ×ˢ U) S from
          fun _ hq ↦ ⟨hq.1.1, hq.2⟩)
    have hd := ContMDiffWithinAt.mfderivWithin
      (f := fun (q : ℝ × M) (y : M) ↦ f (q.1, y)) (g := Prod.snd)
      hc contMDiffWithinAt_snd hp (fun _ hq ↦ hq.2) (m := ∞) (by simp)
      (hU.uniqueMDiffOn (I := 𝓡 n))
    have happ := ContMDiffWithinAt.clm_apply_of_inCoordinates
      (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := ℝ)
      (B₁ := M) (B₂ := ℝ) (E₁ := fun y : M ↦ TangentSpace (𝓡 n) y)
      (E₂ := fun y : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) y)
      (b₁ := Prod.snd) (b₂ := f) (m₀ := p)
      (ϕ := fun q ↦ mfderivWithin (𝓡 n) 𝓘(ℝ, ℝ) (fun y ↦ f (q.1, y)) U q.2)
      (v := fun q ↦ X q.2) hd (hXP p hp) (hf p hp)
    have hsnd := contMDiff_snd_tangentBundle_modelSpace (n := ∞) ℝ 𝓘(ℝ, ℝ)
    exact (hsnd _).comp_contMDiffWithinAt p happ
  apply hWithin.congr
  intro p hp
  simp only [mvfderivWithin, mvfderiv, mfderivWithin_of_isOpen hU hp.2]

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem contMDiffOn_flow_connection_pairing (F : RicciFlow n M J)
    {X Y Z : (y : M) → TangentSpace (𝓡 n) y} (hU : IsOpen U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (F.metric p.1).inner p.2
        ((F.connection p.1).connection Y p.2 (X p.2)) (Z p.2)) (J ×ˢ U) := by
  have hmetric {P Q : (y : M) → TangentSpace (𝓡 n) y}
      (hP : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) U)
      (hQ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Q) U) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M ↦ (F.metric p.1).inner p.2 (P p.2) (Q p.2)) (J ×ˢ U) := by
    have hP' : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun p : ℝ × M ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (P p.2))
        (J ×ˢ U) := hP.comp contMDiffOn_snd (fun _ hp ↦ hp.2)
    have hQ' : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun p : ℝ × M ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (Q p.2))
        (J ×ˢ U) := hQ.comp contMDiffOn_snd (fun _ hp ↦ hp.2)
    intro p hp
    have hm := (F.smooth p ⟨hp.1, mem_univ p.2⟩).mono
      (show J ×ˢ U ⊆ J ×ˢ univ from fun q hq ↦ ⟨hq.1, mem_univ q.2⟩)
    have he : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
        (fun q ↦ Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) q.2
          ((F.metric q.1).inner q.2 (P q.2) (Q q.2))) (J ×ˢ U) p :=
      hm.clm_bundle_apply₂ (hP' p hp) (hQ' p hp)
    simp only [Bundle.contMDiffWithinAt_totalSpace] at he
    exact he.2
  have hbr {P Q : (y : M) → TangentSpace (𝓡 n) y}
      (hP : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) U)
      (hQ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Q) U) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (VectorField.mlieBracket (𝓡 n) P Q)) U := by
    intro x hx
    have hP' := (hP x hx).contMDiffAt (hU.mem_nhds hx)
    have hQ' := (hQ x hx).contMDiffAt (hU.mem_nhds hx)
    let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M := by
      apply IsManifold.of_le (n := (↑(⊤ : ℕ∞) : ℕ∞ω))
      simpa [minSmoothness_eq_infty] using
        (minSmoothness_monotone (𝕜 := ℝ)
          (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)))
    let : IsManifold (𝓡 n) (∞ + 1) M := by
      simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
    exact (hP'.mlieBracket_vectorField (m := ⊤) (n := ⊤) hQ' (by simp)).contMDiffWithinAt
  have h1 := contMDiffOn_mvfderiv_spatial hU (hmetric hY hZ) hX
  have h2 := contMDiffOn_mvfderiv_spatial hU (hmetric hZ hX) hY
  have h3 := contMDiffOn_mvfderiv_spatial hU (hmetric hX hY) hZ
  have hb1 := hmetric (hbr hX hY) hZ
  have hb2 := hmetric (hbr hY hZ) hX
  have hb3 := hmetric (hbr hZ hX) hY
  have hs := (((((h1.add h2).sub h3).add hb1).sub hb2).add hb3).div_const (2 : ℝ)
  apply hs.congr
  intro p hp
  have hk := koszul_pairing (F.connection p.1)
    ((hX.contMDiffAt (hU.mem_nhds hp.2)).mdifferentiableAt (by simp))
    ((hY.contMDiffAt (hU.mem_nhds hp.2)).mdifferentiableAt (by simp))
    ((hZ.contMDiffAt (hU.mem_nhds hp.2)).mdifferentiableAt (by simp))
  apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
  simpa only [Pi.add_apply, Pi.sub_apply, mul_comm] using! hk

end PoincareConjecture.RicciFlowAnalysis
