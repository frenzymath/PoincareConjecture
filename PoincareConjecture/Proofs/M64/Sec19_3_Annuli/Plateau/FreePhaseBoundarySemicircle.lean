import PoincareConjecture.Proofs.M64.Mathlib.HalfDiskStrongGraph
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseBoundaryGraphApproximation














noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Manifold SchwartzMap

namespace PoincareConjecture

open Proofs.M58

private theorem coordinate_eLpNorm_tendsto {m : ℕ} {X : Type*}
    [MeasurableSpace X] {mu : Measure X} {g : ℕ → X → EuclideanSpace ℝ (Fin m)}
    (h : Tendsto (fun j => eLpNorm (g j) 2 mu) atTop (𝓝 0)) (a : Fin m) :
    Tendsto (fun j => eLpNorm (fun z => g j z a) 2 mu) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
  intro j
  exact eLpNorm_mono (fun z => PiLp.norm_apply_le (g j z) a)

namespace M64FreeWeakPhaseAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {Robs : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "basis" => EuclideanSpace.basisFun (Fin 2) ℝ





theorem lower_halfDisk_semicircle_data
    (A : M64FreeWeakPhaseAnnulus (n := n) e Robs c0 c1 H0 H1 k D)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.annulus.map S)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (hH0 : ∀ y, H0 (y + curvePeriod) = H0 y + D)
    (hH1 : ∀ y, H1 (y + curvePeriod) = H1 y + D)
    {x H epsilon R : ℝ} (hHpos : 0 < H) (hx : H < x)
    (hP : x + H < curvePeriod) (hH : H < 1)
    (hepsilon : 0 < epsilon) (hRH : R ≤ H) :
    let u := fun z => e (A.annulus.map (z + annulusPoint x 0))
    let V := fun i z => A.annulus.column i (z + annulusPoint x 0)
    let b := fun s => e (c0 (A.label0 (s + x)))
    ∀ᵐ r ∂volume.restrict (Icc epsilon R), ∀ a : Fin m,
      MemLp (fun theta => u (r • angularPoint theta) a)
        2 (volume.restrict (Icc (0 : ℝ) Real.pi)) ∧
      (∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2),
        (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
          V i z a * test z + u z a * fderiv ℝ test z (basis i)) =
          r * (∫ theta in (0 : ℝ)..Real.pi,
            u (r • angularPoint theta) a * test (r • angularPoint theta) * angularPoint theta i) -
          (basis 1) i * ∫ s in (-r)..r, b s a * test (s • basis 0)) ∧
      MemLp (fun theta => -r * Real.sin theta * V 0 (r • angularPoint theta) a +
        r * Real.cos theta * V 1 (r • angularPoint theta) a)
          2 (volume.restrict (Icc (0 : ℝ) Real.pi)) ∧
      ∃ v : ℝ → ℝ, AbsolutelyContinuousOnInterval v 0 Real.pi ∧
        (v =ᵐ[volume.restrict (Icc (0 : ℝ) Real.pi)]
          fun theta => u (r • angularPoint theta) a) ∧
        v 0 = b r a ∧ v Real.pi = b (-r) a ∧
        ∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
          v t - v s = ∫ theta in s..t,
            -r * Real.sin theta * V 0 (r • angularPoint theta) a +
              r * Real.cos theta * V 1 (r • angularPoint theta) a := by
  obtain ⟨hu, hV, hb, f, hf, hval, hcol, htrace⟩ :=
    A.lower_halfDisk_graph_approximation he hA hc0 hc1 hH0 hH1 hHpos hx hP hH
  apply ae_all_iff.mpr
  intro a
  have hder (j : ℕ) (z : LoopPlane) (i : Fin 2) :
      fderiv ℝ (fun y => f j y a) z (basis i) =
        (fderiv ℝ (f j) z (EuclideanSpace.single i 1)) a := by
    let L : E →L[ℝ] ℝ := EuclideanSpace.proj a
    have hd := (L.hasFDerivAt.comp z ((hf j).differentiable one_ne_zero z).hasFDerivAt).fderiv
    change fderiv ℝ (L ∘ f j) z (basis i) = _
    rw [hd, EuclideanSpace.basisFun_apply]
    rfl
  have hline (s : ℝ) : s • basis 0 = annulusPoint s 0 := by
    ext i
    fin_cases i <;> simp [annulusPoint, EuclideanSpace.basisFun_apply]
  apply m64HalfDisk_strong_graph_extract hepsilon hRH
    (fun z => e (A.annulus.map (z + annulusPoint x 0)) a)
    (fun i z => A.annulus.column i (z + annulusPoint x 0) a)
    (fun s => e (c0 (A.label0 (s + x))) a)
    (hu.eval_piLp a) (fun i => (hV i).eval_piLp a) (hb.eval_piLp a)
    (fun j z => f j z a) (fun j => by
      change ContDiff ℝ 1 ((EuclideanSpace.proj (𝕜 := ℝ) a) ∘ f j)
      exact (EuclideanSpace.proj (𝕜 := ℝ) a).contDiff.comp (hf j))
  · simpa only [Pi.sub_def, PiLp.sub_apply] using coordinate_eLpNorm_tendsto hval a
  · intro i
    simpa only [hder, PiLp.sub_apply] using coordinate_eLpNorm_tendsto (hcol i) a
  · simpa only [hline, PiLp.sub_apply] using coordinate_eLpNorm_tendsto htrace a

end M64FreeWeakPhaseAnnulus
end PoincareConjecture
