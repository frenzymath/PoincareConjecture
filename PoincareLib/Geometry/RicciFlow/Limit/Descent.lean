import PoincareLib.Geometry.RicciFlow.Basic
import PoincareLib.Geometry.Riemannian.Connection.ChangeMetric
import PoincareLib.Geometry.Riemannian.Curvature.LocalIsometryRicci
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Ricci flows descended from a local isometry cover

Local Ricci flows on a fixed covering family of spatial local diffeomorphisms
give the Ricci-flow equation for a jointly smooth metric family on the covered
manifold. One reference Levi-Civita datum supplies total connection data by
changing its metric. Metric preservation is required only on the time domain,
and the equation retains within-domain derivatives at included endpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareMT.RicciFlow

/-- Descend the local equations to the prescribed metric family. The single
reference connection remains an explicit input for a separate construction
from compatible local connections. -/
theorem exists_of_covering_local_diffeomorphisms
    {n : ℕ} {ι : Type*} [Nonempty ι] {P : ι → Type*} {N : Type*}
    [∀ i, TopologicalSpace (P i)] [TopologicalSpace N]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i)]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [∀ i, IsManifold (𝓡 n) ∞ (P i)] [IsManifold (𝓡 n) ∞ N]
    {J : Set ℝ} (F : ∀ i, RicciFlow n (P i) J)
    (gN : ℝ → RiemannianMetric n N)
    (hgN : RiemannianMetric.IsSmoothFamilyOn gN J)
    (t₀ : ℝ) (D₀ : LeviCivitaData (gN t₀))
    (q : ∀ i, P i → N)
    (hq : ∀ i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (q i))
    (hcover : ∀ y, ∃ i x, q i x = y)
    (hpres : ∀ t ∈ J, ∀ i (x : P i) (a b : TangentSpace (𝓡 n) x),
      ((F i).metric t).inner x a b = (gN t).inner (q i x)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x a)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x b)) :
    ∃ FN : RicciFlow n N J, FN.metric = gN := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  let D : ∀ t, LeviCivitaData (gN t) := fun t => D₀.withMetric (gN t)
  refine ⟨{
    metric := gN
    connection := D
    interval := (F i₀).interval
    nontrivial := (F i₀).nontrivial
    smooth := hgN
    equation := ?_ }, rfl⟩
  intro t ht y u v
  obtain ⟨i, x, rfl⟩ := hcover y
  let A := (hq i x).mfderivToContinuousLinearEquiv (by simp)
  obtain ⟨a, ha⟩ := A.surjective u
  obtain ⟨b, hb⟩ := A.surjective v
  have ha' : mfderiv (𝓡 n) (𝓡 n) (q i) x a = u := ha
  have hb' : mfderiv (𝓡 n) (𝓡 n) (q i) x b = v := hb
  have hRicci := ((F i).connection t).ricci_eq_of_local_isometry (D t)
    isOpen_univ (hq i).contMDiff.contMDiffOn
    (fun z _ a b => hpres t ht i z a b) (mem_univ x) a b
  have hderiv := (F i).equation t ht x a b
  rw [hRicci, ha', hb'] at hderiv
  apply hderiv.congr_of_mem ?_ ht
  intro s hs
  simpa only [ha', hb'] using (hpres s hs i x a b).symm

end PoincareMT.RicciFlow
