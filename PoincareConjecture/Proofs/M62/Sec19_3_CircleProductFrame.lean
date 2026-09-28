import PoincareConjecture.Proofs.M62.Sec19_3_CircleIdentities
import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductCharts
import PoincareConjecture.Proofs.M09.ChartVectorField
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62.CircleProductCharts

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {circumference : ℝ} {C : CircleGeometry circumference}

def productChartField (P : CircleProductCharts C n M)
    (p : M) (v : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (q : P.Point) : TangentSpace (𝓡 (n + 1)) q :=
  (P.split q).symm
    (PoincareConjecture.Proofs.M09.chartVectorField p v q.1, r • C.frame q.2)

theorem productChartField_split (P : CircleProductCharts C n M)
    (p : M) (v : EuclideanSpace ℝ (Fin n)) (r : ℝ) (q : P.Point) :
    P.split q (P.productChartField p v r q) =
      (PoincareConjecture.Proofs.M09.chartVectorField p v q.1, r • C.frame q.2) :=
  (P.split q).apply_symm_apply _

theorem productChartField_contMDiffOn (P : CircleProductCharts C n M)
    (p : M) (v : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)).tangent ∞
      (fun q : P.Point =>
        (⟨q, P.productChartField p v r q⟩ : TangentBundle (𝓡 (n + 1)) P.Point))
      {q : P.Point | q.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source} := by
  let := P.chartedSpace
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.Point → M) :=
    contMDiff_fst.comp P.to_product_smooth
  have hsnd : ContMDiff (𝓡 (n + 1)) (𝓡 1) ∞ (Prod.snd : P.Point → C.Point) :=
    contMDiff_snd.comp P.to_product_smooth
  have hsplit (z : P.Point) (V : TangentSpace ((𝓡 n).prod (𝓡 1)) z) :
      P.split z (mfderiv (M' := P.Point) ((𝓡 n).prod (𝓡 1)) (𝓡 (n + 1))
        (id : M × C.Point → P.Point) z V) = (V.1, V.2) := by
    apply Prod.ext
    · rw [P.split_space]
      have h := mfderiv_comp_apply (f := (id : M × C.Point → P.Point))
        (g := (Prod.fst : P.Point → M)) z
        (hfst.mdifferentiableAt (by simp))
        (P.from_product_smooth.mdifferentiableAt (by simp)) V
      simpa +instances only [Function.comp_def, id_eq, mfderiv_fst,
        ContinuousLinearMap.coe_fst'] using! h.symm
    · rw [P.split_circle]
      have h := mfderiv_comp_apply (f := (id : M × C.Point → P.Point))
        (g := (Prod.snd : P.Point → C.Point)) z
        (hsnd.mdifferentiableAt (by simp))
        (P.from_product_smooth.mdifferentiableAt (by simp)) V
      simpa +instances only [Function.comp_def, id_eq, mfderiv_snd,
        ContinuousLinearMap.coe_snd'] using! h.symm
  intro q hq
  let X := PoincareConjecture.Proofs.M09.chartVectorField p v
  have hX : ContMDiffAt (𝓡 n) (𝓡 n).tangent ∞ (T% X) q.1 :=
    (PoincareConjecture.Proofs.M09.chartVectorField_smooth p v).contMDiffAt
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).open_source.mem_nhds hq)
  have hcircle : ContMDiffAt (𝓡 1) (𝓡 1).tangent ∞
      (fun z : C.Point => (⟨z, r • C.frame z⟩ : TangentBundle (𝓡 1) C.Point)) q.2 :=
    ((circle_identities C).frame_smooth q.2).const_smul_section (a := r)
  have hprod : ContMDiffAt ((𝓡 n).prod (𝓡 1)) ((𝓡 n).prod (𝓡 1)).tangent ∞
      (fun z : M × C.Point =>
        (⟨z, (X z.1, r • C.frame z.2)⟩ :
          TangentBundle ((𝓡 n).prod (𝓡 1)) (M × C.Point))) q :=
    contMDiff_equivTangentBundleProd_symm.contMDiffAt.comp q
      ((hX.comp q contMDiffAt_fst).prodMk (hcircle.comp q contMDiffAt_snd))
  have h := ((P.from_product_smooth.contMDiff_tangentMap (m := ∞) (by simp)).contMDiffAt.comp
    q hprod).comp q (P.to_product_smooth q)
  apply ContMDiffAt.contMDiffWithinAt
  apply h.congr_of_eventuallyEq
  filter_upwards [] with z
  dsimp only [Function.comp_apply, id_eq, tangentMap]
  rw [TotalSpace.mk_inj]
  apply (P.split z).injective
  erw [hsplit]
  exact P.productChartField_split p v r z

theorem productChartField_exists (P : CircleProductCharts C n M)
    (p : M) (q : P.Point)
    (hq : q.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (V : TangentSpace (𝓡 (n + 1)) q) :
    ∃ (v : EuclideanSpace ℝ (Fin n)) (r : ℝ), P.productChartField p v r q = V := by
  let L := (mdifferentiable_chart (I := 𝓡 n) p).mfderiv hq
  have hnonzero : C.frame q.2 ≠ 0 := by
    intro he
    have hu := (circle_identities C).frame_unit q.2
    simp only [he, map_zero] at hu
    norm_num at hu
  obtain ⟨r, hr⟩ := exists_smul_eq_of_finrank_eq_one
    (by simp [TangentSpace] : Module.finrank ℝ (TangentSpace (𝓡 1) q.2) = 1)
    hnonzero (P.split q V).2
  refine ⟨L (P.split q V).1, r, ?_⟩
  apply (P.split q).injective
  rw [P.productChartField_split, hr]
  apply Prod.ext
  · have hi : (mfderiv (𝓡 n) (𝓡 n)
        (chartAt (EuclideanSpace ℝ (Fin n)) p) q.1).IsInvertible := ⟨L, rfl⟩
    exact hi.inverse_apply_self (P.split q V).1
  · rfl

end PoincareConjecture.M62.CircleProductCharts
