import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusWeakClassicalColumns
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryCrossEnergy

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

theorem m64ObservedMetric_symmetric_pair_of_mDifferentiableAt
    (g : RiemannianMetric n M) (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v)
    {f : LoopPlane → M} {p : LoopPlane} (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f p)
    (i j : Fin 2) :
    Q (f p) (fderiv ℝ (e ∘ f) p (EuclideanSpace.single i 1))
        (fderiv ℝ (e ∘ f) p (EuclideanSpace.single j 1)) +
      Q (f p) (fderiv ℝ (e ∘ f) p (EuclideanSpace.single j 1))
        (fderiv ℝ (e ∘ f) p (EuclideanSpace.single i 1)) =
          2 * m60AreaGram g f p i j := by
  let v (i : Fin 2) := mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.single i 1)
  let L := mfderiv (𝓡 n) (𝓡 m) e (f p)
  have hd := mfderiv_comp (I := 𝓡 2) (I' := 𝓡 n) (I'' := 𝓡 m)
    p (he.mdifferentiable (by simp) _) hf
  rw [mfderiv_eq_fderiv] at hd
  have hcol (i : Fin 2) : fderiv ℝ (e ∘ f) p (EuclideanSpace.single i 1) = L (v i) :=
    congrArg (fun T => T (EuclideanSpace.single i 1)) hd
  rw [hcol i, hcol j]
  have h := hdiag (f p) (v i + v j)
  simp only [map_add, add_apply] at h
  rw [hdiag (f p) (v i), hdiag (f p) (v j), g.symm (f p) (v j) (v i)] at h
  simp only [m60AreaGram, EuclideanSpace.basisFun_apply]
  change Q (f p) (L (v i)) (L (v j)) + Q (f p) (L (v j)) (L (v i)) =
    2 * g.inner (f p) (v i) (v j)
  linarith only [h]

namespace M64ObservedWeakAnnulus

variable {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

theorem stress_eq_ae_of_contMDiffOn
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map S) (r : ℝ) :
    ∀ᵐ p ∂mu,
      r * Q (A.map p) (A.column 0 p) (A.column 0 p) -
          r⁻¹ * Q (A.map p) (A.column 1 p) (A.column 1 p) =
        r * m60AreaGram g A.map p 0 0 - r⁻¹ * m60AreaGram g A.map p 1 1 ∧
      r⁻¹ * (Q (A.map p) (A.column 0 p) (A.column 1 p) +
          Q (A.map p) (A.column 1 p) (A.column 0 p)) =
        2 * r⁻¹ * m60AreaGram g A.map p 0 1 := by
  have hcol := A.classical_columns_of_contMDiffOn he hA
  filter_upwards [hcol 0, hcol 1, ae_restrict_mem isOpen_interior.measurableSet]
    with p h0 h1 hp
  have hd := (hA.contMDiffAt (isOpen_interior.mem_nhds hp)).mdifferentiableAt (by simp)
  rw [h0, h1, m64ObservedMetric_diagonal_of_mDifferentiableAt g e he Q hdiag hd 0,
    m64ObservedMetric_diagonal_of_mDifferentiableAt g e he Q hdiag hd 1,
    m64ObservedMetric_symmetric_pair_of_mDifferentiableAt g e he Q hdiag hd 0 1]
  exact ⟨rfl, by ring⟩

theorem gram_integrable_of_contMDiffOn
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖Q q‖ ≤ K)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map S) (i j : Fin 2) :
    Integrable (fun p => m60AreaGram g A.map p i j) mu := by
  have hi := ((A.column_pair_integrable Q hQ hei hb i j).add
    (A.column_pair_integrable Q hQ hei hb j i)).div_const 2
  apply hi.congr
  have hcol := A.classical_columns_of_contMDiffOn he hA
  filter_upwards [hcol i, hcol j, ae_restrict_mem isOpen_interior.measurableSet]
    with p hi hj hp
  change (Q (A.map p) (A.column i p) (A.column j p) +
    Q (A.map p) (A.column j p) (A.column i p)) / 2 = _
  rw [hi, hj, m64ObservedMetric_symmetric_pair_of_mDifferentiableAt g e he Q hdiag
    ((hA.contMDiffAt (isOpen_interior.mem_nhds hp)).mdifferentiableAt (by simp)) i j]
  ring

end M64ObservedWeakAnnulus

end PoincareConjecture
