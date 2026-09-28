import PoincareConjecture.Proofs.M34.Standard.ConnectionVelocityJets
import PoincareConjecture.Proofs.M03.ConnectionVariation
import PoincareConjecture.Proofs.M03.ConnectionDifference
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CanonicalDomain











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

variable {n : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]




theorem canonicalDomain_hasDerivAt_connection :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J : Set ℝ} (F : RicciFlow n U J) {t : ℝ}, t ∈ interior J →
      ∀ (p x : U) (i j : Fin n),
        HasDerivAt (F := V n)
          (fun s => ((F.connection s).connection
            (fun _ : U => EuclideanSpace.single j 1) x
              (EuclideanSpace.single i 1) : V n))
          (canonicalDomain_connectionVelocity U hU (F.metric t) (F.connection t)
            p (x : V n) i j) t := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro J F t ht p x i j
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : U → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let e := fun i : Fin n => EuclideanSpace.single i (1 : ℝ)
  let E := fun v : V n => fun _ : U => v
  have hE (v : V n) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V n)) ∞
      (fun y : U => TotalSpace.mk' (V n) (E := TangentSpace (𝓡 n)) y (E v y)) univ :=
    (constantChart_contMDiff_const_field (𝓡 n) (canonicalOpen_chart_eq hU) v).contMDiffOn
  let W := fun s => (F.connection s).connection (E (e j)) x (e i)
  let C := fun i j k : Fin n =>
    fderiv ℝ (fun z => (F.connection t).ricci ((extChartAt (𝓡 n) x).symm z)
      (e j) (e k)) ((extChartAt (𝓡 n) x) x) (e i) -
      (F.connection t).ricci x ((F.connection t).connection (E (e j)) x (e i)) (e k) -
      (F.connection t).ricci x (e j) ((F.connection t).connection (E (e k)) x (e i))
  have hW : HasDerivAt W (deriv W t) t := by
    exact (Proofs.M03.ricciFlow_connection_variation_pairing F ht isOpen_univ
      (E (e i)) (E (e j)) (E 0) (hE _) (hE _) (hE _) (mem_univ x)).1
  have hpair (k : Fin n) :
      (F.metric t).inner x (deriv W t) (e k) = -C i j k - C j k i + C k i j := by
    exact (Proofs.M03.ricciFlow_connection_variation_pairing F ht isOpen_univ
      (E (e i)) (E (e j)) (E (e k)) (hE _) (hE _) (hE _) (mem_univ x)).2
  let tr := trivializationAt (V n) (TangentSpace (𝓡 n)) p
  let L := tr.continuousLinearMapAt ℝ x
  have hxtr : x ∈ tr.baseSet := by
    rw [constantChart_tangent_baseSet (𝓡 n) (canonicalOpen_chart_eq hU)]
    trivial
  have hL (v : TangentSpace (𝓡 n) x) : L v = (v : V n) := by
    rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ tr hxtr]
    exact congrArg Prod.snd
      (constantChart_tangent_coordinates (𝓡 n) (canonicalOpen_chart_eq hU) p x v)
  have hmodel : HasDerivAt (fun s => (W s : V n)) (L (deriv W t)) t := by
    have hh := L.hasFDerivAt.comp_hasDerivAt t hW
    simpa only [Function.comp_def, hL] using hh
  let G := (F.metric t).pullbackCoefficients (extChartAt (𝓡 n) p).symm (x : V n)
  have hxt : (x : V n) ∈ (extChartAt (𝓡 n) p).target := by
    rw [canonicalOpen_extChart_target (𝕜 := ℝ) hU p]
    exact x.property
  have hnative : L (deriv W t) = G.inverse
      (∑ k : Fin n, (-C i j k - C j k i + C k i j) • EuclideanSpace.proj k) := by
    apply Proofs.M03.native_derivative_of_lowered_pairings
      ((F.metric t).isInvertible_chartCoefficients p hxt)
    intro k
    rw [RiemannianMetric.pullbackCoefficients_canonicalChart U hU, hL]
    exact hpair k
  have hrx : (extChartAt (𝓡 n) p).symm (x : V n) = x :=
    canonicalOpen_chart_symm_apply hU p x
  have hC (a b c : Fin n) : C a b c = ∑ l : Fin n,
      canonicalDomain_covariantCurvatureArray U hU (F.metric t) (F.connection t)
        p (x : V n) a l l b c := by
    have hh := canonicalDomain_covariantCurvatureArray_ricci_trace U hU
      (F.metric t) (F.connection t) p (x : V n) x.property a b c
    rw [hrx] at hh
    exact hh.symm
  rw [hnative] at hmodel
  simpa only [canonicalDomain_connectionVelocity, ← hC] using hmodel




theorem canonicalDomain_hasDerivAt_connection_difference :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J') {t : ℝ},
      t ∈ interior J → t ∈ interior J' → ∀ (p x : U) (i j : Fin n),
        HasDerivAt (F := V n)
          (fun s => (CovariantDerivative.difference
            (F.connection s).connection (F'.connection s).connection x
              (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) : V n))
          (canonicalDomain_connectionVelocity U hU (F.metric t) (F.connection t)
              p (x : V n) i j -
            canonicalDomain_connectionVelocity U hU (F'.metric t) (F'.connection t)
              p (x : V n) i j) t := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro J J' F F' t ht ht' p x i j
  have hd := HasDerivAt.sub (F := V n)
    (canonicalDomain_hasDerivAt_connection U hU F ht p x i j)
    (canonicalDomain_hasDerivAt_connection U hU F' ht' p x i j)
  apply hd.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro s
  have hY := (constantChart_contMDiff_const_field (𝓡 n) (canonicalOpen_chart_eq hU)
    (EuclideanSpace.single j (1 : ℝ))).mdifferentiableAt (x := x) (by simp)
  have hh := IsCovariantDerivativeOn.difference_apply
    (F.connection s).connection.isCovariantDerivativeOnUniv
    (F'.connection s).connection.isCovariantDerivativeOnUniv (mem_univ x) hY
  exact congrArg (fun L => L (EuclideanSpace.single i 1)) hh

end PoincareConjecture.M34
