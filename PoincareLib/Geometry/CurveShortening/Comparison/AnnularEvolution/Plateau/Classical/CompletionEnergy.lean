import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weighted.AnnulusEnergyIdentity
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Annulus.WeakClassicalColumns
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Variable.ModulusContinuity

/-! A C1 classical completion has exactly the original observed weak
energy. Source: MT Lemma 19.15; M64 closed-C1 admission derivation.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareMT.M64ObservedWeakAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

/-- Almost-everywhere agreement with a classical C1 annulus preserves the original weak
energy and identifies it with the actual intrinsic Gram integral, for every modulus. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem weightedEnergy_eq_of_classical_completion
    (W : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {g : RiemannianMetric n M} (A : M64Annulus g c0 c1)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      B q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v)
    (hmap : A.map =ᵐ[volume.restrict S] W.map)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map S) (r : ℝ) :
    W.weightedEnergy B r = ∫ p in m64AnnulusDomain,
      (r * m60AreaGram g A.map p 0 0 + r⁻¹ * m60AreaGram g A.map p 1 1) / 2 := by
  obtain ⟨O, hO, hcols, -⟩ := W.with_map_ae A.map hmap
  have hOae : O.map =ᵐ[volume.restrict S] W.map := hO ▸ hmap
  have henergy := W.weightedEnergy_eq_of_map_ae O hOae hcols B r
  have hOC1 : ContMDiffOn (𝓡 2) (𝓡 n) 1 O.map S := hO ▸ hA
  have hc := O.classical_columns_of_contMDiffOn he hOC1
  rw [hO] at hc
  exact henergy.symm.trans
    (m64ObservedWeakAnnulus_seed_weightedEnergy_eq A e he B hdiag O hO hc r)

end PoincareMT.M64ObservedWeakAnnulus
