import PoincareConjecture.Proofs.M35.RawFlow.SectionalPlanes
import PoincareConjecture.Proofs.M35.Uniqueness.RawDistanceExhaustion
import PoincareConjecture.Proofs.M10.ScalarBound









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

open M04

abbrev StandardSectionalPair := modelOrthonormalPairs 3

noncomputable def rawSectionalRayleigh {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) (t : ℝ)
    (z : StandardCapSpace × StandardSectionalPair) : ℝ :=
  (G.flow.connection t).sectionalCurvature z.1 z.2.val.1 z.2.val.2

private theorem continuousOn_sectionalRayleigh_euclidean {n : ℕ} {J : Set ℝ}
    (F : RicciFlow n (EuclideanSpace ℝ (Fin n)) J) :
    ContinuousOn (fun p : (ℝ × EuclideanSpace ℝ (Fin n)) ×
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
      (F.connection p.1.1).sectionalCurvature p.1.2 p.2.1 p.2.2)
      ((J ×ˢ univ) ×ˢ modelOrthonormalPairs n) := by
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) (0 : V)
  have hbase : e.baseSet = univ := rfl
  have he (y v : V) : e.symmL ℝ y v = v := by
    simp only [e, TangentBundle.symmL_model_space]
    rfl
  have h := continuousOn_flow_sectionalRayleigh_trivialization F (0 : V)
  change ContinuousOn (fun p : (ℝ × V) × (V × V) =>
    (F.connection p.1.1).curvatureTensor p.1.2
      (e.symmL ℝ p.1.2 p.2.1) (e.symmL ℝ p.1.2 p.2.2)
      (e.symmL ℝ p.1.2 p.2.1) (e.symmL ℝ p.1.2 p.2.2) /
      metricGram (F.metric p.1.1) p.1.2
        (e.symmL ℝ p.1.2 p.2.1) (e.symmL ℝ p.1.2 p.2.2))
    ((J ×ˢ e.baseSet) ×ˢ modelOrthonormalPairs n) at h
  simp only [he, hbase] at h
  exact h

theorem continuousOn_rawSectionalRayleigh {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) :
    ContinuousOn (Function.uncurry (rawSectionalRayleigh G)) (Ico 0 G.lifetime ×ˢ univ) := by
  have h := continuousOn_sectionalRayleigh_euclidean G.flow
  have hc : Continuous (fun z : ℝ × (StandardCapSpace × StandardSectionalPair) =>
      ((z.1, z.2.1), z.2.2.val)) := by fun_prop
  have hm : MapsTo (fun z : ℝ × (StandardCapSpace × StandardSectionalPair) =>
      ((z.1, z.2.1), z.2.2.val)) (Ico 0 G.lifetime ×ˢ univ)
      ((Ico 0 G.lifetime ×ˢ univ) ×ˢ modelOrthonormalPairs 3) :=
    fun z hz => ⟨⟨hz.1, mem_univ _⟩, z.2.2.property⟩
  convert! h.comp hc.continuousOn hm using 1

theorem rawSectionalRayleigh_initial_nonneg {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) (z : StandardCapSpace × StandardSectionalPair) :
    0 ≤ rawSectionalRayleigh G 0 z := by
  have htransport (g h : RiemannianMetric 3 StandardCapSpace)
      (D : LeviCivitaData g) (D' : LeviCivitaData h) (hg : g = h) (hD : HEq D D') :
      D.curvatureTensor z.1 z.2.val.1 z.2.val.2 z.2.val.1 z.2.val.2 =
        D'.curvatureTensor z.1 z.2.val.1 z.2.val.2 z.2.val.1 z.2.val.2 := by
    subst h
    cases eq_of_heq hD
    rfl
  apply div_nonneg
  · rw [htransport _ _ _ _ G.initial_metric G.initial_connection]
    exact g₀.nonnegative_sectional z.1 z.2.val.1 z.2.val.2
  · exact (metricGram_pos_of_modelPair (G.flow.metric 0) z.1 z.2.property).le

theorem rawSectionalRayleigh_abs_le {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) (t : ℝ) (z : StandardCapSpace × StandardSectionalPair) :
    |rawSectionalRayleigh G t z| ≤ (G.flow.connection t).curvatureTensorNorm z.1 :=
  (G.flow.connection t).abs_sectionalCurvature_le_curvatureTensorNorm z.1 z.2.val.1 z.2.val.2

theorem rawSectionalRayleigh_reaction_bound {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {K t : ℝ}
    (hK : ∀ x, (G.flow.connection t).curvatureTensorNorm x ≤ K)
    (z : StandardCapSpace × StandardSectionalPair) :
    (G.flow.connection t).scalarCurvature z.1 - 2 * rawSectionalRayleigh G t z ≤ 11 * K := by
  have hq := (abs_le.mp ((rawSectionalRayleigh_abs_le G t z).trans (hK z.1))).1
  have hs := (le_abs_self _).trans (M10.abs_scalarCurvature_le
    (G.flow.metric t) (G.flow.connection t) z.1)
  norm_num at hs
  linarith [hK z.1]

end PoincareConjecture.M35.Uniqueness
