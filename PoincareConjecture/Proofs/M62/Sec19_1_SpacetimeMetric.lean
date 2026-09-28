import PoincareConjecture.Proofs.M62.Sec19_1_SpacetimeCharts
import PoincareConjecture.Proofs.M01.NormalizationMetric
import PoincareConjecture.Proofs.M01.ConnectionExistence
import PoincareConjecture.Proofs.M04.MetricPairings
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}



theorem exists_spacetimeMetric (F : RicciFlow n M (Set.Icc a b))
    (C : SpacetimeCharts n M a b) :
    ∃ g : RiemannianMetric (n + 1) C.Point,
      ∀ (q : C.Point) (V W : TangentSpace (𝓡 (n + 1)) q),
        g.inner q V W =
          (F.metric q.2).inner q.1 (C.split q V).1 (C.split q W).1 +
            (C.split q V).2 * (C.split q W).2 := by
  let := C.chartedSpace
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let A : (q : C.Point) → TangentSpace (𝓡 (n + 1)) q →L[ℝ]
      TangentSpace (𝓡 n) q.1 := fun q =>
    (ContinuousLinearMap.fst ℝ _ ℝ).comp (C.split q).toContinuousLinearMap
  let T : (q : C.Point) → TangentSpace (𝓡 (n + 1)) q →L[ℝ] ℝ := fun q =>
    (ContinuousLinearMap.snd ℝ _ ℝ).comp (C.split q).toContinuousLinearMap
  let Q : (q : C.Point) → TangentSpace (𝓡 (n + 1)) q →L[ℝ]
      TangentSpace (𝓡 (n + 1)) q →L[ℝ] ℝ := fun q =>
    ((A q).precomp ℝ).comp (((F.metric q.2).inner q.1).comp (A q)) +
      ((T q).precomp ℝ).comp ((ContinuousLinearMap.mul ℝ ℝ).comp (T q))
  have hQ (q : C.Point) (V W : TangentSpace (𝓡 (n + 1)) q) :
      Q q V W = (F.metric q.2).inner q.1 (C.split q V).1 (C.split q W).1 +
        (C.split q V).2 * (C.split q W).2 := rfl
  have hpos (q : C.Point) (V : TangentSpace (𝓡 (n + 1)) q) (hV : V ≠ 0) :
      0 < Q q V V := by
    rw [hQ]
    by_cases hs : (C.split q V).1 = 0
    · have ht : (C.split q V).2 ≠ 0 := by
        intro ht
        apply hV
        apply (C.split q).injective
        ext <;> simp [hs, ht]
      simpa only [hs, map_zero, zero_apply, zero_add] using
        mul_self_pos.mpr ht
    · exact add_pos_of_pos_of_nonneg ((F.metric q.2).pos q.1 _ hs)
        (mul_self_nonneg _)
  have hspace : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞
      (Prod.fst : C.Point → M) :=
    contMDiff_fst.comp C.to_product_smooth
  have hclock : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞
      (fun q : C.Point => (q.2 : ℝ)) :=
    (contMDiff_subtype_val.comp contMDiff_snd).comp C.to_product_smooth
  have hg : ContMDiff (𝓡 (n + 1))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (fun q : C.Point => TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (E := fun p : M => TangentSpace (𝓡 n) p →L[ℝ] TangentSpace (𝓡 n) p →L[ℝ] ℝ)
        q.1 ((F.metric q.2).inner q.1)) := by
    rw [← contMDiffOn_univ]
    exact F.smooth.comp (hclock.prodMk hspace).contMDiffOn
      (fun q _ => ⟨Ioo_subset_Icc_self q.2.property, mem_univ _⟩)
  refine ⟨{
    inner := Q
    symm := fun q V W => by rw [hQ, hQ, (F.metric q.2).symm, mul_comm]
    pos := hpos
    isVonNBounded := fun q => m01_isVonNBounded_of_posDef (F := E) (Q q) (hpos q)
    contMDiff := ?_
  }, hQ⟩
  intro p
  let e := trivializationAt E (TangentSpace (𝓡 (n + 1)) : C.Point → Type _) p
  have hp : p ∈ e.baseSet := mem_baseSet_trivializationAt E _ p
  let S : E → (q : C.Point) → TangentSpace (𝓡 (n + 1)) q :=
    fun v q => e.symmL ℝ q v
  have hS (v : E) : ContMDiffAt (𝓡 (n + 1)) ((𝓡 (n + 1)).prod 𝓘(ℝ, E)) ∞
      (fun q : C.Point => TotalSpace.mk' E q (S v q)) p := by
    rw [e.contMDiffAt_section_iff hp]
    apply (contMDiffAt_const (c := v)).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds hp] with q hq
    simpa only [S, Trivialization.symmL_apply _ hq] using
      congrArg Prod.snd (e.apply_mk_symm hq v)
  have hA (v : E) : ContMDiffAt (𝓡 (n + 1))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun q : C.Point => TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        q.1 (A q (S v q))) p := by
    have h := ((hspace p).mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates
      (hS v) (hspace p)
    apply h.congr_of_eventuallyEq
    filter_upwards [] with q
    congr 1
    exact C.split_space q (S v q)
  have hT (v : E) : ContMDiffAt (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞
      (fun q : C.Point => T q (S v q)) p := by
    have h := ((hclock p).mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates
      (hS v) (hclock p)
    have hh := (contMDiff_snd_tangentBundle_modelSpace (n := ∞) ℝ 𝓘(ℝ, ℝ)
      _).comp p h
    apply hh.congr_of_eventuallyEq
    filter_upwards [] with q
    exact C.split_time q (S v q)
  rw [contMDiffAt_section]
  apply M04.contMDiffAt_clm_of_apply
  intro v
  apply M04.contMDiffAt_clm_of_apply
  intro w
  have hpair : ContMDiffAt (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : C.Point => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) q.1
        ((F.metric q.2).inner q.1 (A q (S v q)) (A q (S w q)))) p :=
    (hg p).clm_bundle_apply₂ (hA v) (hA w)
  have hsum := ((Bundle.contMDiffAt_totalSpace.mp hpair).2).add ((hT v).mul (hT w))
  apply hsum.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hp] with q hq
  simp only [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ hq hq (mem_univ q)]
  simp only [Bundle.Trivial.eq_trivialization, Bundle.Trivial.linearMapAt_trivialization,
    LinearMap.id_apply, Q, add_apply, ContinuousLinearMap.comp_apply,
    Pi.add_apply, Pi.mul_apply, S]
  rw [Trivialization.symmL_apply e hq, Trivialization.symmL_apply e hq]
  rfl



theorem nonempty_spacetimeData_of_charts [T2Space M] [SecondCountableTopology M]
    (F : RicciFlow n M (Set.Icc a b)) (C : SpacetimeCharts n M a b) :
    Nonempty (SpacetimeData F) := by
  obtain ⟨g, hg⟩ := exists_spacetimeMetric F C
  obtain ⟨D⟩ := m01_exists_leviCivitaData g
  exact ⟨{ charts := C, metric := g, connection := D, metric_eq := hg }⟩

end PoincareConjecture.M62
