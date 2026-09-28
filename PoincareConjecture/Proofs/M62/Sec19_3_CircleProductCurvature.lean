import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductConnection
import PoincareConjecture.Proofs.M62.Sec19_1_CurvaturePairing










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 800000 in



theorem circleProduct_curvatureTensor
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {circumference : ℝ} (C : CircleGeometry circumference)
    (P : CircleProductCharts C n M)
    (G : RiemannianMetric (n + 1) P.Point) (DG : LeviCivitaData G)
    (hG : ∀ (q : P.Point) (V W : TangentSpace (𝓡 (n + 1)) q),
      G.inner q V W = g.inner q.1 (P.split q V).1 (P.split q W).1 +
        C.metricOnPoints.inner q.2 (P.split q V).2 (P.split q W).2)
    (q : P.Point) (V W Z T : TangentSpace (𝓡 (n + 1)) q) :
    DG.curvatureTensor q V W Z T =
      D.curvatureTensor q.1 (P.split q V).1 (P.split q W).1
        (P.split q Z).1 (P.split q T).1 := by
  let := P.chartedSpace
  let E := EuclideanSpace ℝ (Fin n)
  let p := q.1
  let X := fun u : E => PoincareConjecture.Proofs.M09.chartVectorField p u
  let A := fun (u : E) (a : ℝ) => P.productChartField p u a
  have hp : p ∈ (chartAt E p).source := mem_chart_source E p
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.Point → M) :=
    contMDiff_fst.comp P.to_product_smooth
  have hopen : IsOpen {z : P.Point | z.1 ∈ (chartAt E p).source} :=
    (chartAt E p).open_source.preimage hfst.continuous
  have hX (u : E) : ContMDiffOn (𝓡 n) (𝓡 n).tangent ∞ (T% (X u))
      (chartAt E p).source := PoincareConjecture.Proofs.M09.chartVectorField_smooth p u
  have hA (u : E) (a : ℝ) : ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)).tangent ∞
      (T% (A u a)) {z : P.Point | z.1 ∈ (chartAt E p).source} :=
    P.productChartField_contMDiffOn p u a
  have hconn (u v : E) (a b : ℝ) (z : P.Point)
      (hz : z.1 ∈ (chartAt E p).source) :
      P.split z (DG.connection (A v b) z (A u a z)) =
        (D.connection (X v) z.1 (X u z.1), 0) :=
    circleProduct_chart_connection g D C P G DG hG p u v a b z hz
  have hcross (u v w z : E) (a b c d : ℝ) :
      G.inner q (DG.connection (A v b) q (A u a q))
        (DG.connection (A z d) q (A w c q)) =
      g.inner p (D.connection (X v) p (X u p)) (D.connection (X z) p (X w p)) := by
    rw [hG, hconn u v a b q hp, hconn w z c d q hp]
    simp only [map_zero, add_zero]
    rfl
  have hd (u v w z : E) (a b c d : ℝ) :
      mvfderiv (𝓡 (n + 1))
        (fun y => G.inner y (DG.connection (A w c) y (A v b y)) (A z d y)) q (A u a q) =
      mvfderiv (𝓡 n)
        (fun x => g.inner x (D.connection (X w) x (X v x)) (X z x)) p (X u p) := by
    let f : M → ℝ := fun x => g.inner x (D.connection (X w) x (X v x)) (X z x)
    have hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f p :=
      ((M04.contMDiffOn_connection_pairing D (chartAt E p).open_source
        (hX v) (hX w) (hX z)).contMDiffAt
          ((chartAt E p).open_source.mem_nhds hp)).mdifferentiableAt (by simp)
    have heq : (fun y => G.inner y (DG.connection (A w c) y (A v b y)) (A z d y))
        =ᶠ[𝓝 q] (f ∘ (Prod.fst : P.Point → M)) := by
      filter_upwards [hopen.mem_nhds hp] with y hy
      rw [hG, hconn v w b c y hy]
      dsimp only [A]
      rw [P.productChartField_split]
      simp only [map_zero, zero_apply, add_zero]
      rfl
    have heq' := congrArg (fun L => L (A u a q))
      (heq.mfderiv_eq (I := 𝓡 (n + 1)) (I' := 𝓘(ℝ, ℝ)))
    have hc := mvfderiv_comp_apply (f := (Prod.fst : P.Point → M)) (g := f) q hf
      (hfst.mdifferentiableAt (by simp)) (A u a q)
    calc
      _ = mvfderiv (𝓡 (n + 1)) (f ∘ Prod.fst) q (A u a q) := heq'
      _ = _ := by
        rw [hc, ← P.split_space]
        change mvfderiv (𝓡 n) f p (P.split q (P.productChartField p u a q)).1 = _
        rw [P.productChartField_split]
  have hformula (u v w z : E) (a b c d : ℝ) :
      DG.curvatureTensor q (A u a q) (A v b q) (A w c q) (A z d q) =
        D.curvatureTensor p (X u p) (X v p) (X w p) (X z p) := by
    have h := curvatureTensor_pairing_of_commuting DG hopen
      (hA u a) (hA v b) (hA w c) (hA z d) hp
      (P.productChartField_bracket p u v a b q hp)
    have hs := curvatureTensor_pairing_of_commuting D (chartAt E p).open_source
      (hX u) (hX v) (hX w) (hX z) hp
      (PoincareConjecture.Proofs.M09.chartVectorField_bracket p u v p hp)
    rw [hd, hcross, hd, hcross] at h
    exact h.trans hs.symm
  obtain ⟨v, r, hV⟩ := P.productChartField_exists p q hp V
  obtain ⟨w, s, hW⟩ := P.productChartField_exists p q hp W
  obtain ⟨z, l, hZ⟩ := P.productChartField_exists p q hp Z
  obtain ⟨t, k, hT⟩ := P.productChartField_exists p q hp T
  rw [← hV, ← hW, ← hZ, ← hT]
  rw [P.productChartField_split, P.productChartField_split,
    P.productChartField_split, P.productChartField_split]
  exact hformula v w z t r s l k

end PoincareConjecture.M62
