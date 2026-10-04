import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Cylinder.Jets.CylinderAllOrderBounds

/-!
# Finite jets at varying centered points

The gluing proof compares finitely many jets at an actual source point
and its image. Taylor composition handles varying smooth chart germs
without a common chart radius. Source: the compactness argument in
Proposition 15.2, pp. 353-354, in its finite-jet form.
-/

set_option autoImplicit false

open Filter
open scoped ContDiff Topology

namespace PoincareMT.M45

variable {ι E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Every fixed derivative order converges at the chosen moving point.
The tail on which an input order is available may depend on that order.
Derivation: GluingCompactness.md, applying Proposition 15.2, pp. 353-354. -/
def PointJetsConverge (f : ι → E → F) (x : ι → E)
    (f0 : E → F) (x0 : E) (l : Filter ι) : Prop :=
  ∀ m : ℕ, Tendsto (fun i => iteratedFDeriv ℝ m (f i) (x i)) l
    (𝓝 (iteratedFDeriv ℝ m f0 x0))

/-- Taylor composition is continuous in each finite collection of its
coefficient slots. Derivation: GluingCompactness.md, applying
Proposition 15.2, pp. 353-354. -/
theorem tendsto_taylorComp
    {p : ι → FormalMultilinearSeries ℝ F G} {p0 : FormalMultilinearSeries ℝ F G}
    {q : ι → FormalMultilinearSeries ℝ E F} {q0 : FormalMultilinearSeries ℝ E F}
    {l : Filter ι}
    (hp : ∀ m, Tendsto (fun i => p i m) l (𝓝 (p0 m)))
    (hq : ∀ m, Tendsto (fun i => q i m) l (𝓝 (q0 m))) (m : ℕ) :
    Tendsto (fun i => (p i).taylorComp (q i) m) l (𝓝 (p0.taylorComp q0 m)) := by
  classical
  unfold FormalMultilinearSeries.taylorComp
  apply tendsto_finsetSum
  intro c _
  have hinner : Tendsto (fun i => fun j : Fin c.length => q i (c.partSize j)) l
      (𝓝 (fun j : Fin c.length => q0 (c.partSize j))) :=
    tendsto_pi_nhds.mpr fun j => hq (c.partSize j)
  exact (c.compAlongOrderedFinpartitionL ℝ E F G).continuousAt_uncurry_of_multilinear.tendsto.comp
    ((hp c.length).prodMk_nhds hinner)

namespace PointJetsConverge

variable {f : ι → E → F} {x : ι → E} {f0 : E → F} {x0 : E} {l : Filter ι}

/-- A convergent finite jet has an order-dependent eventual norm bound.
Derivation: GluingCompactness.md, applying Proposition 15.2, pp. 353-354. -/
theorem bounded (h : PointJetsConverge f x f0 x0 l) (m : ℕ) :
    l.IsBoundedUnder (· ≤ ·) (fun i => ‖iteratedFDeriv ℝ m (f i) (x i)‖) :=
  (h m).norm.isBoundedUnder_le

/-- The zero-jet limit is convergence of the actual map values.
Derivation: GluingCompactness.md, applying Proposition 15.2, pp. 353-354. -/
theorem values (h : PointJetsConverge f x f0 x0 l) :
    Tendsto (fun i => f i (x i)) l (𝓝 (f0 x0)) := by
  have hc : Continuous (fun L : E [×0]→L[ℝ] F => L (fun i => Fin.elim0 i)) := by fun_prop
  simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using hc.continuousAt.tendsto.comp (h 0)

/-- Differentiating shifts the convergent finite jets by one order.
Derivation: GluingCompactness.md, applying Proposition 15.2, pp. 353-354. -/
theorem fderiv (h : PointJetsConverge f x f0 x0 l) :
    PointJetsConverge (fun i => _root_.fderiv ℝ (f i)) x (_root_.fderiv ℝ f0) x0 l := by
  intro m
  have he := (continuousMultilinearCurryRightEquiv' ℝ m E F).continuous.continuousAt.tendsto.comp
    (h (m + 1))
  simpa only [iteratedFDeriv_succ_eq_comp_right, Function.comp_def,
    LinearIsometryEquiv.apply_symm_apply] using he

/-- Pairing two actual smooth germs pairs their limiting jets.
Derivation: GluingCompactness.md, applying Proposition 15.2, pp. 353-354. -/
theorem prodMk {g : ι → E → G} {g0 : E → G}
    (hf : PointJetsConverge f x f0 x0 l) (hg : PointJetsConverge g x g0 x0 l)
    (hfs : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hgs : ∀ i, ContDiffAt ℝ ∞ (g i) (x i))
    (hf0 : ContDiffAt ℝ ∞ f0 x0) (hg0 : ContDiffAt ℝ ∞ g0 x0) :
    PointJetsConverge (fun i y => (f i y, g i y)) x (fun y => (f0 y, g0 y)) x0 l := by
  intro m
  have he := (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin m => E) F G).continuous
    |>.continuousAt.tendsto.comp ((hf m).prodMk_nhds (hg m))
  simpa only [iteratedFDeriv_prodMk (hfs _) (hgs _) (by exact_mod_cast le_top),
    iteratedFDeriv_prodMk hf0 hg0 (by exact_mod_cast le_top),
    Function.comp_def, ContinuousMultilinearMap.prodL_apply,
    ContinuousMultilinearMap.prodEquiv] using he

/-- Varying composition preserves limits of the exact finite jets.
The outer jets are evaluated at the actual inner images.
Derivation: GluingCompactness.md, applying Proposition 15.2, pp. 353-354. -/
theorem comp {g : ι → F → G} {g0 : F → G}
    (hf : PointJetsConverge f x f0 x0 l)
    (hg : PointJetsConverge g (fun i => f i (x i)) g0 (f0 x0) l)
    (hfs : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hgs : ∀ i, ContDiffAt ℝ ∞ (g i) (f i (x i)))
    (hf0 : ContDiffAt ℝ ∞ f0 x0) (hg0 : ContDiffAt ℝ ∞ g0 (f0 x0)) :
    PointJetsConverge (fun i => g i ∘ f i) x (g0 ∘ f0) x0 l := by
  intro m
  have he := tendsto_taylorComp (p := fun i => ftaylorSeries ℝ (g i) (f i (x i)))
    (p0 := ftaylorSeries ℝ g0 (f0 x0))
    (q := fun i => ftaylorSeries ℝ (f i) (x i)) (q0 := ftaylorSeries ℝ f0 x0) hg hf m
  simpa only [iteratedFDeriv_comp (hgs _) (hfs _) (by exact_mod_cast le_top),
    iteratedFDeriv_comp hg0 hf0 (by exact_mod_cast le_top)] using he

/-- A fixed smooth finite-jet operator preserves the pointwise jet
limit, including all its derivatives. Derivation: GluingCompactness.md,
applying Proposition 15.2, pp. 353-354. -/
theorem smooth_postcompose {g : F → G}
    (hf : PointJetsConverge f x f0 x0 l)
    (hfs : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hgs : ∀ i, ContDiffAt ℝ ∞ g (f i (x i)))
    (hf0 : ContDiffAt ℝ ∞ f0 x0) (hg0 : ContDiffAt ℝ ∞ g (f0 x0)) :
    PointJetsConverge (fun i => g ∘ f i) x (g ∘ f0) x0 l := by
  apply hf.comp (fun m => ?_) hfs hgs hf0 hg0
  exact (hg0.continuousAt_iteratedFDeriv (by exact_mod_cast le_top)).tendsto.comp hf.values

end PointJetsConverge

end PoincareMT.M45
