import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductBracket
import PoincareConjecture.Proofs.M04.KoszulPairing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 800000 in

theorem circleProduct_chart_connection
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {circumference : ℝ} (C : CircleGeometry circumference)
    (P : CircleProductCharts C n M)
    (G : RiemannianMetric (n + 1) P.Point) (DG : LeviCivitaData G)
    (hG : ∀ (q : P.Point) (V W : TangentSpace (𝓡 (n + 1)) q),
      G.inner q V W = g.inner q.1 (P.split q V).1 (P.split q W).1 +
        C.metricOnPoints.inner q.2 (P.split q V).2 (P.split q W).2)
    (p : M) (v w : EuclideanSpace ℝ (Fin n)) (r s : ℝ) (q : P.Point)
    (hq : q.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    P.split q (DG.connection (P.productChartField p w s) q
      (P.productChartField p v r q)) =
        (D.connection (PoincareConjecture.Proofs.M09.chartVectorField p w) q.1
          (PoincareConjecture.Proofs.M09.chartVectorField p v q.1), 0) := by
  let := P.chartedSpace
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let E := EuclideanSpace ℝ (Fin n)
  let X := fun u : E => PoincareConjecture.Proofs.M09.chartVectorField p u
  let A := fun (u : E) (a : ℝ) => P.productChartField p u a
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.Point → M) :=
    contMDiff_fst.comp P.to_product_smooth
  have hopen : IsOpen {z : P.Point | z.1 ∈ (chartAt E p).source} :=
    (chartAt E p).open_source.preimage hfst.continuous
  have hA (u : E) (a : ℝ) : ContMDiffAt (𝓡 (n + 1)) (𝓡 (n + 1)).tangent ∞
      (T% (A u a)) q :=
    (P.productChartField_contMDiffOn p u a).contMDiffAt (hopen.mem_nhds hq)
  have hX (u : E) : ContMDiffAt (𝓡 n) (𝓡 n).tangent ∞ (T% (X u)) q.1 :=
    (PoincareConjecture.Proofs.M09.chartVectorField_smooth p u).contMDiffAt
      ((chartAt E p).open_source.mem_nhds hq)
  have hinner (u v : E) (a b : ℝ) (z : P.Point) :
      G.inner z (A u a z) (A v b z) = g.inner z.1 (X u z.1) (X v z.1) + a * b := by
    rw [hG]
    dsimp only [A]
    rw [P.productChartField_split, P.productChartField_split]
    simp only [map_smul, smul_apply, smul_eq_mul, (circle_identities C).frame_unit,
      mul_one, X]
    rw [mul_comm a b]
  have hd (u v w : E) (a b c : ℝ) :
      mvfderiv (𝓡 (n + 1)) (fun z => G.inner z (A v b z) (A w c z)) q (A u a q) =
        mvfderiv (𝓡 n) (fun x => g.inner x (X v x) (X w x)) q.1 (X u q.1) := by
    let f : M → ℝ := fun x => g.inner x (X v x) (X w x)
    have hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f q.1 :=
      ((hX v).inner_bundle (hX w)).mdifferentiableAt (by simp)
    have he : (fun z => G.inner z (A v b z) (A w c z)) =
        fun z : P.Point => f z.1 + b * c := funext (hinner v w b c)
    rw [he]
    change mvfderiv (𝓡 (n + 1)) (fun z => (f ∘ Prod.fst) z + b * c) q (A u a q) = _
    rw [mvfderiv_fun_add (hf.comp q (hfst.mdifferentiableAt (by simp)))
      mdifferentiableAt_const, mvfderiv_const, add_zero]
    have h := mvfderiv_comp_apply (f := (Prod.fst : P.Point → M)) (g := f) q hf
      (hfst.mdifferentiableAt (by simp)) (A u a q)
    change mvfderiv (𝓡 (n + 1)) (f ∘ Prod.fst) q (A u a q) = _
    rw [h, ← P.split_space]
    change mvfderiv (𝓡 n) f q.1 (P.split q (P.productChartField p u a q)).1 = _
    rw [P.productChartField_split]
  have hb (u v : E) (a b : ℝ) :
      VectorField.mlieBracket (𝓡 (n + 1)) (A u a) (A v b) q = 0 :=
    P.productChartField_bracket p u v a b q hq
  have hbx (u v : E) : VectorField.mlieBracket (𝓡 n) (X u) (X v) q.1 = 0 :=
    PoincareConjecture.Proofs.M09.chartVectorField_bracket p u v q.1 hq
  have hpair (z : E) (l : ℝ) :
      G.inner q (DG.connection (A w s) q (A v r q)) (A z l q) =
        g.inner q.1 (D.connection (X w) q.1 (X v q.1)) (X z q.1) := by
    have h := M04.koszul_pairing DG (X := A v r) (Y := A w s) (Z := A z l)
      ((hA v r).mdifferentiableAt (by simp)) ((hA w s).mdifferentiableAt (by simp))
      ((hA z l).mdifferentiableAt (by simp))
    have hs := M04.koszul_pairing D (X := X v) (Y := X w) (Z := X z)
      ((hX v).mdifferentiableAt (by simp)) ((hX w).mdifferentiableAt (by simp))
      ((hX z).mdifferentiableAt (by simp))
    simp only [hb, map_zero, zero_apply, sub_zero, add_zero, hd] at h
    simp only [hbx, map_zero, zero_apply, sub_zero, add_zero] at hs
    linarith only [h, hs]
  let U := DG.connection (A w s) q (A v r q)
  let V := (P.split q).symm (D.connection (X w) q.1 (X v q.1), 0)
  have htest (W : TangentSpace (𝓡 (n + 1)) q) : G.inner q U W = G.inner q V W := by
    obtain ⟨z, l, hz⟩ := P.productChartField_exists p q hq W
    rw [← hz]
    have hV : G.inner q V (A z l q) =
        g.inner q.1 (D.connection (X w) q.1 (X v q.1)) (X z q.1) := by
      rw [hG]
      dsimp only [V, A]
      rw [ContinuousLinearEquiv.apply_symm_apply, P.productChartField_split]
      simp only [map_zero, zero_apply, add_zero]
      rfl
    exact (hpair z l).trans hV.symm
  have heq : U = V := by
    by_contra hne
    have hzero : G.inner q (U - V) (U - V) = 0 := by
      rw [(G.inner q).map_sub U V]
      change G.inner q U (U - V) - G.inner q V (U - V) = 0
      exact sub_eq_zero.mpr (htest (U - V))
    exact (ne_of_gt (G.pos q (U - V) (sub_ne_zero.mpr hne))) hzero
  change P.split q U = _
  rw [heq]
  exact (P.split q).apply_symm_apply _

end PoincareConjecture.M62
