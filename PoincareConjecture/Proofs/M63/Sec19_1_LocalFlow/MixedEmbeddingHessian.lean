import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.EmbeddingHessianVector
import PoincareConjecture.Proofs.M04.ShiNormalCoordinates

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u v w

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {V : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V]

local notation "W" => EuclideanSpace ℝ ι

theorem flow_coordinateHessian_mixed_pullback_contDiffOn {a b : ℝ}
    (F : RicciFlow n M (Icc a b)) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set V} (hU : IsOpen U) {ρ : V → M}
    (hρ : ContMDiffOn 𝓘(ℝ, V) (𝓡 n) ∞ ρ U) :
    ContDiffOn ℝ ∞
      (fun z : (ℝ × V) × (V × V) => coordinateHessian (F.connection z.1.1) e (ρ z.1.2)
        (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ z.1.2 z.2.1)
        (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ z.1.2 z.2.2)) ((Icc a b ×ˢ U) ×ˢ univ) := by
  let S : Set ((ℝ × V) × (V × V)) := (Icc a b ×ˢ U) ×ˢ univ
  let H : (ℝ × V) × V → W := fun z => coordinateHessian (F.connection z.1.1) e (ρ z.1.2)
    (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ z.1.2 z.2)
    (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ z.1.2 z.2)
  have hH : ContDiffOn ℝ ∞ H ((Icc a b ×ˢ U) ×ˢ univ) :=
    flow_coordinateHessian_pullback_contDiffOn F he hU hρ
  have hsum : ContDiffOn ℝ ∞ (fun z : (ℝ × V) × (V × V) => H (z.1, z.2.1 + z.2.2)) S :=
    hH.comp (contDiff_fst.prodMk (contDiff_snd.fst.add contDiff_snd.snd)).contDiffOn
      (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hfst : ContDiffOn ℝ ∞ (fun z : (ℝ × V) × (V × V) => H (z.1, z.2.1)) S :=
    hH.comp (contDiff_fst.prodMk contDiff_snd.fst).contDiffOn
      (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hsnd : ContDiffOn ℝ ∞ (fun z : (ℝ × V) × (V × V) => H (z.1, z.2.2)) S :=
    hH.comp (contDiff_fst.prodMk contDiff_snd.snd).contDiffOn
      (fun z hz => ⟨hz.1, mem_univ _⟩)
  apply (((hsum.sub hfst).sub hsnd).const_smul (1 / 2 : ℝ)).congr
  intro z _hz
  change coordinateHessian (F.connection z.1.1) e (ρ z.1.2)
      (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ z.1.2 z.2.1)
      (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ z.1.2 z.2.2) =
    (1 / 2 : ℝ) • (H (z.1, z.2.1 + z.2.2) - H (z.1, z.2.1) - H (z.1, z.2.2))
  dsimp only [H]
  erw [map_add]
  ext i
  let D := F.connection z.1.1
  let p := ρ z.1.2
  let X := mfderiv 𝓘(ℝ, V) (𝓡 n) ρ z.1.2 z.2.1
  let Y := mfderiv 𝓘(ℝ, V) (𝓡 n) ρ z.1.2 z.2.2
  let f : M → ℝ := fun q => e q i
  have hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f :=
    (EuclideanSpace.proj i).contDiff.contMDiff.comp he
  obtain ⟨A, hA⟩ := (M04.isSmoothCovariantTensor_hessian D hf).1 p
  have hrep (v w : TangentSpace (𝓡 n) p) : D.hessian f p v w = A ![v, w] :=
    hA ![v, w]
  have hadd_left (v w r : TangentSpace (𝓡 n) p) :
      D.hessian f p (v + w) r = D.hessian f p v r + D.hessian f p w r := by
    rw [hrep, hrep, hrep]
    simpa only [Matrix.vecCons] using A.cons_add ![r] v w
  have hadd_right (v w r : TangentSpace (𝓡 n) p) :
      D.hessian f p v (w + r) = D.hessian f p v w + D.hessian f p v r := by
    rw [hrep, hrep, hrep]
    simpa only [MultilinearMap.curryLeft_apply, Matrix.vecCons] using
      (A.curryLeft v).cons_add ![] w r
  have hsym : D.hessian f p X Y = D.hessian f p Y X :=
    M04.hessian_symm_on D isOpen_univ hf.contMDiffOn (mem_univ p) X Y
  have hpol : D.hessian f p (X + Y) (X + Y) =
      (D.hessian f p X X + D.hessian f p X Y) +
        (D.hessian f p Y X + D.hessian f p Y Y) := by
    rw [hadd_left, hadd_right, hadd_right]
  change D.hessian f p X Y =
    (1 / 2 : ℝ) * (D.hessian f p (X + Y) (X + Y) - D.hessian f p X X - D.hessian f p Y Y)
  linarith only [hpol, hsym]

end PoincareConjecture.M63
