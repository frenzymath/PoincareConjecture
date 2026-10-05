import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Compatibility
import PoincareLib.Geometry.RicciFlow.Basic
import PoincareLib.Geometry.RicciFlow.Local.Connection.CurvatureIndependence

/-!
# Constructing a Ricci flow from local time representatives

Equality of whole metrics identifies their actual curvature evaluations,
without identifying their retained connection records. Local flow
representatives then give the smoothness and equation of an assembled
family. This is the union step in Morgan-Tian Theorem 12.5, p. 297;
see the reviewed common-compact-lifetime derivation in the task records.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Set Filter

namespace PoincareMT.M34

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Whole-metric equality identifies actual Ricci evaluations even for
different retained connections (Theorem 12.5, p. 297, union construction). -/
theorem ricci_eq_of_metric_eq {g g' : RiemannianMetric n M} (h : g = g')
    (D : LeviCivitaData g) (D' : LeviCivitaData g') (x : M)
    (u v : TangentSpace (𝓡 n) x) : D.ricci x u v = D'.ricci x u v := by
  subst g'
  exact D.ricci_eq D' x u v

/-- Whole-metric equality identifies actual full-curvature norms even for
different retained connections (Theorem 12.5, p. 297, union construction). -/
theorem curvatureTensorNorm_eq_of_metric_eq {g g' : RiemannianMetric n M} (h : g = g')
    (D : LeviCivitaData g) (D' : LeviCivitaData g') (x : M) :
    D.curvatureTensorNorm x = D'.curvatureTensorNorm x := by
  subst g'
  exact D.curvatureTensorNorm_eq D' x

/-- A metric family locally represented by actual flows is a flow on its
nontrivial interval, with its supplied connections (Theorem 12.5, p. 297). -/
noncomputable def flowOfLocalRepresentatives (J : Set ℝ)
    (g : ℝ → RiemannianMetric n M) (D : (t : ℝ) → LeviCivitaData (g t))
    (hinterval : J.OrdConnected) (hne : J.Nontrivial)
    (hloc : ∀ t ∈ J, ∃ K : Set ℝ, ∃ F : RicciFlow n M K,
      t ∈ K ∧ K ∈ 𝓝[J] t ∧ g =ᶠ[𝓝[J] t] F.metric) : RicciFlow n M J where
  metric := g
  connection := D
  interval := hinterval
  nontrivial := hne
  smooth := by
    intro p hp
    obtain ⟨K, F, htK, hK, heq⟩ := hloc p.1 hp.1
    have hprod : K ×ˢ (univ : Set M) ∈ 𝓝[J ×ˢ univ] p :=
      nhdsWithin_prod hK (by simp)
    have hproj : Tendsto (fun q : ℝ × M => q.1) (𝓝[J ×ˢ univ] p) (𝓝[J] p.1) :=
      continuousWithinAt_fst.tendsto_nhdsWithin (fun _ hq => hq.1)
    have hs := (F.smooth p ⟨htK, mem_univ p.2⟩).mono_of_mem_nhdsWithin hprod
    apply hs.congr_of_eventuallyEq_of_mem _ hp
    filter_upwards [heq.comp_tendsto hproj] with q hq
    change g q.1 = F.metric q.1 at hq
    rw [hq]
  equation t ht x u v := by
    obtain ⟨K, F, htK, hK, heq⟩ := hloc t ht
    have heqt : g t = F.metric t := heq.eq_of_nhdsWithin ht
    rw [ricci_eq_of_metric_eq heqt (D t) (F.connection t)]
    have hd := (F.equation t htK x u v).mono_of_mem_nhdsWithin hK
    apply hd.congr_of_eventuallyEq_of_mem _ ht
    filter_upwards [heq] with s hs
    exact congrArg (fun m : RiemannianMetric n M => m.inner x u v) hs

end PoincareMT.M34
