import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Transport.Shift
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.UniversalProperty
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.RegularDomain

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology
open Poincare.Geometry.Manifold.RegularLevel

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] [IsManifold (𝓡 (n + 1)) ∞ M]
  {g : RiemannianMetric (n + 1) M} (D : LeviCivitaData g) {f : M → ℝ}
  (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
  {a : ℝ} (ha : ∀ x, a < f x → 1 ≤ g.inner x (D.gradient f x) (D.gradient f x))
  {Φ : ℝ → M → M} (h0 : ∀ x, Φ 0 x = x)
  (hΦ : ∀ x, IsMIntegralCurve (fun t => Φ t x) (D.boundedNormalizedGradient f))
  (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
  (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 (n + 1))) (𝓡 (n + 1)) ∞ (Function.uncurry Φ))

include ha h0 hΦ hadd hs

theorem exists_normalizedGradient_levelDiffeomorph {c d : ℝ} (hc : a < c) (hd : a < d) :
    let U := g.regularDomain hf
    let hreg := g.regularDomain_regular hf
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf U hreg n c
    letI := openLevelSetChartedSpace hf U hreg n d
    ∃ e : openLevelSet f U c ≃ₘ⟮𝓡 n, 𝓡 n⟯ openLevelSet f U d,
      ∀ z, openLevelIncl f U d (e z) = Φ (d - c) (openLevelIncl f U c z) := by
  let U := g.regularDomain hf
  let hreg := g.regularDomain_regular hf
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf U hreg n c
  let := openLevelSetChartedSpace hf U hreg n d
  have hshift (x : M) (t : ℝ) (hx : a < f x) (ht : a < f x + t) :
      f (Φ t x) = f x + t := by
    simpa only [h0 x] using D.potential_boundedNormalizedGradient_eq_add hf (hΦ x) ha
      (by simpa only [h0 x] using hx) (by simpa only [h0 x] using ht)
  have hU (x : M) (hx : a < f x) : x ∈ U := by
    change 0 < Real.sqrt (g.inner x (D.gradient f x) (D.gradient f x))
    exact Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (ha x hx))
  have hlevel {r s : ℝ} (hr : a < r) (hs' : a < s) (x : M) (hx : f x = r) :
      f (Φ (s - r) x) = s := by
    rw [hshift x (s - r) (hx ▸ hr) (by rw [hx]; linarith), hx]
    ring
  let toD : openLevelSet f U c → openLevelSet f U d := fun z =>
    ⟨⟨Φ (d - c) (openLevelIncl f U c z),
      hU _ (by rw [hlevel hc hd (openLevelIncl f U c z) z.2]; exact hd)⟩,
      hlevel hc hd _ z.2⟩
  let toC : openLevelSet f U d → openLevelSet f U c := fun z =>
    ⟨⟨Φ (c - d) (openLevelIncl f U d z),
      hU _ (by rw [hlevel hd hc (openLevelIncl f U d z) z.2]; exact hc)⟩,
      hlevel hd hc _ z.2⟩
  refine ⟨{
    toFun := toD
    invFun := toC
    left_inv := ?_
    right_inv := ?_
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }, fun _ => rfl⟩
  · intro z
    apply Subtype.ext
    apply Subtype.ext
    change Φ (c - d) (Φ (d - c) (openLevelIncl f U c z)) = openLevelIncl f U c z
    rw [← hadd, sub_add_sub_cancel, sub_self, h0]
  · intro z
    apply Subtype.ext
    apply Subtype.ext
    change Φ (d - c) (Φ (c - d) (openLevelIncl f U d z)) = openLevelIncl f U d z
    rw [← hadd, sub_add_sub_cancel, sub_self, h0]
  · intro z
    apply (contMDiffAt_into_openLevelSet_iff hf n d U hreg toD z).mpr
    exact ((hs.comp (contMDiff_const.prodMk contMDiff_id))
      (openLevelIncl f U c z)).comp z (contMDiff_openLevelIncl hf U hreg n c z)
  · intro z
    apply (contMDiffAt_into_openLevelSet_iff hf n c U hreg toC z).mpr
    exact ((hs.comp (contMDiff_const.prodMk contMDiff_id))
      (openLevelIncl f U d z)).comp z (contMDiff_openLevelIncl hf U hreg n d z)

end PoincareConjecture.LeviCivitaData
