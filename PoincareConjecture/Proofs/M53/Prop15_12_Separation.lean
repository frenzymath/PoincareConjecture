import PoincareConjecture.Proofs.M53.Prop15_12_AssemblyInputs
import PoincareConjecture.Proofs.M53.Prop15_12_GeneratorRestriction
import PoincareConjecture.Proofs.M53.Prop15_12_SurfaceComparison
import PoincareConjecture.Proofs.M53.Prop15_12_ModelBoundaryParity
import PoincareConjecture.Proofs.M53.Prop15_12_PointParityTransport
import PoincareConjecture.Proofs.M53.Prop15_12_RelativeClass
import PoincareConjecture.Proofs.M53.Prop15_12_SphereChart
import PoincareConjecture.Proofs.M53.Mathlib.ChartCylinder

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Set Metric Topology
open PoincareConjecture.Proofs.M02.Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M53

theorem sphere_complement_not_isPreconnected
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (S : SmoothEmbeddedNullHomotopicSphere (M := M)) :
    ¬ IsPreconnected (range S.sphere)ᶜ := by
  classical
  intro hconn
  obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty
    (E := EuclideanSpace ℝ (Fin 3)) (x := 0) (r := 1) |>.mpr (by norm_num)
  let x0 : UnitTwoSphere := ⟨x, hx⟩
  let E := ULift.{u} (EuclideanSpace ℝ (Fin 2))
  obtain ⟨e, hx0, he0, hslice⟩ := sphere_exists_centered_zero_slice_chart S x0
  have h0 : (0 : E × ℝ) ∈ e.target := he0 ▸ e.map_source hx0
  obtain ⟨r, hr, hKt⟩ := e.exists_pos_cylinder_subset_target h0
  let D := closedBall (0 : E) r
  let K := D ×ˢ Icc (-r) r
  let KX := e.symm '' K
  let L := KXᶜ
  let S0 := range S.sphere
  let A := S0 ∪ L
  let Q : Set (E × ℝ) := {z | z.2 = 0} ∪ Kᶜ
  let U := e.target
  let AV : Set U := (Subtype.val : U → E × ℝ) ⁻¹' Q
  let LV : Set U := (Subtype.val : U → E × ℝ) ⁻¹' Kᶜ
  let f : C(U, M) := ⟨fun z => e.symm z, e.symm.continuousOn.domRestrict⟩
  let g : C(U, E × ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
  have hf : IsOpenEmbedding f := e.symm.isOpenEmbedding_restrict
  have hg : IsOpenEmbedding g := e.open_target.isOpenEmbedding_subtypeVal
  have hD : IsCompact D := isCompact_closedBall _ _
  have hK : IsCompact K := hD.prod isCompact_Icc
  have hconv : Convex ℝ K := (convex_closedBall (0 : E) r).prod (convex_Icc (-r) r)
  have hKX : IsCompact KX := hK.image_of_continuousOn (e.symm.continuousOn.mono hKt)
  have hfKr : KX ⊆ range f := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨⟨z, hKt hz⟩, rfl⟩
  have hgKr : K ⊆ range g := fun z hz => ⟨⟨z, hKt hz⟩, rfl⟩
  have hKmem (z : U) : f z ∈ KX ↔ z.val ∈ K := by
    constructor
    · rintro ⟨w, hw, heq⟩
      exact (e.symm.injOn (hKt hw) z.property heq) ▸ hw
    · exact fun hz => ⟨z.val, hz, rfl⟩
  have hfL (z : U) : z ∈ LV ↔ f z ∈ L := (not_congr (hKmem z)).symm
  have hfA (z : U) : z ∈ AV ↔ f z ∈ A := by
    have hs : f z ∈ S0 ↔ z.val.2 = 0 := by
      change e.symm z.val ∈ range S.sphere ↔ z.val.2 = 0
      simpa only [e.right_inv z.property] using
        hslice (e.symm z.val) (e.map_target z.property)
    exact or_congr hs.symm (hfL z)
  have hSA : S0 ⊆ A := subset_union_left
  have hLA : L ⊆ A := subset_union_right
  have hLVA : LV ⊆ AV := fun _ hz => Or.inr hz
  obtain ⟨alpha, halpha⟩ := sphereRelativeBoundary_surjective S 2 (by decide)
    (sphereFundamentalClass S)
  let beta := homologyMap (integralRelativeRestriction hSA) 3 alpha
  let F := homologyMap (integralRelativeMap f (fun z hz => (hfA z).mp hz)) 3
  let : IsIso F := integralRelativeMap_isIso_of_closed_support f hf hfA
    hKX.isClosed hfKr subset_union_right 3
  obtain ⟨b, hb⟩ := (asIso F).toLinearEquiv.surjective beta
  change F b = beta at hb
  let G := homologyMap (integralRelativeMap g (A := AV) (B := Q) (fun _ hz => hz)) 3
  let a := G b
  let c := r / 2
  have hc : 0 < c := half_pos hr
  have h0D : (0 : E) ∈ D := mem_closedBall_self hr.le
  have hp : ((0 : E), c) ∈ K := ⟨h0D, by dsimp [c]; constructor <;> linarith⟩
  have hm : ((0 : E), -c) ∈ K := ⟨h0D, by dsimp [c]; constructor <;> linarith⟩
  let p : U := ⟨(0, c), hKt hp⟩
  let m : U := ⟨(0, -c), hKt hm⟩
  have hQp : Q ⊆ ({g p}ᶜ : Set (E × ℝ)) := subset_compl_singleton_iff.mpr (by
    rintro (hz | hz)
    · exact (ne_of_gt hc) hz
    · exact hz hp)
  have hQm : Q ⊆ ({g m}ᶜ : Set (E × ℝ)) := subset_compl_singleton_iff.mpr (by
    rintro (hz | hz)
    · exact (neg_ne_zero.mpr (ne_of_gt hc)) hz
    · exact hz hm)
  have hAp : A ⊆ ({f p}ᶜ : Set M) :=
    subset_compl_singleton_iff.mpr (fun hz => hQp ((hfA p).mpr hz) rfl)
  have hAm : A ⊆ ({f m}ᶜ : Set M) :=
    subset_compl_singleton_iff.mpr (fun hz => hQm ((hfA m).mpr hz) rfl)
  have hpoint (z : U) (hQz : Q ⊆ ({g z}ᶜ : Set (E × ℝ)))
      (hAz : A ⊆ ({f z}ᶜ : Set M)) :
      Even (homologyMap (integralRelativeRestriction hQz) 3 a) ↔
        Even (homologyMap (integralRelativeRestriction (hSA.trans hAz)) 3 alpha) := by
    have hVz : AV ⊆ ({z}ᶜ : Set U) :=
      subset_compl_singleton_iff.mpr (fun hz => hQz hz rfl)
    have hfp := even_point_restriction_openEmbedding_iff f hf
      (fun y hy => (hfA y).mp hy) z hVz hAz 3 b
    have hgp := even_point_restriction_openEmbedding_iff g hg
      (A := AV) (B := Q) (fun _ hy => hy) z hVz hQz 3 b
    change Even (homologyMap (integralRelativeRestriction hAz) 3 (F b)) ↔ _ at hfp
    rw [hb] at hfp
    have hcomp : homologyMap (integralRelativeRestriction hSA) 3 ≫
        homologyMap (integralRelativeRestriction hAz) 3 =
        homologyMap (integralRelativeRestriction (hSA.trans hAz)) 3 := by
      rw [← homologyMap_comp, integralRelativeRestriction_comp]
    have hbpar : Even (homologyMap (integralRelativeRestriction hAz) 3 beta) ↔
        Even (homologyMap (integralRelativeRestriction (hSA.trans hAz)) 3 alpha) := by
      change Even ((homologyMap (integralRelativeRestriction hSA) 3 ≫
        homologyMap (integralRelativeRestriction hAz) 3) alpha) ↔ _
      rw [hcomp]
    exact hgp.trans (hfp.symm.trans hbpar)
  have hpar : Even (homologyMap (integralRelativeRestriction hQp) 3 a) ↔
      Even (homologyMap (integralRelativeRestriction hQm) 3 a) :=
    (hpoint p hQp hAp).trans
      ((even_threeManifoldRelativeRestriction_iff_of_isPreconnected S0 hconn alpha
        (hSA.trans hAp) (hSA.trans hAm)).trans (hpoint m hQm hAm).symm)
  have hdim : Module.finrank ℝ (E × ℝ) = 3 := by simp [E, Module.finrank_prod]
  obtain ⟨ep⟩ := nonempty_integralThreePointHomology_equiv_int hdim ((0 : E), c)
  obtain ⟨em⟩ := nonempty_integralThreePointHomology_equiv_int hdim ((0 : E), -c)
  have hmodel : Even (integralTripleBoundary Q Kᶜ subset_union_right 2 a) := by
    apply even_planeExterior_tripleBoundary_of_point_parity K hK hconv c hc hp hm 2 ep em a
    let T := homologyMap (integralRelativeRestriction
      (planeExterior_subset_twoPuncture K c hc hp hm)) 3
    let rp := integralSupportHomologyRestriction
      (subset_union_left : ({((0 : E), c)} : Set (E × ℝ)) ⊆ {(0, c)} ∪ {(0, -c)}) 3
    let rm := integralSupportHomologyRestriction
      (subset_union_right : ({((0 : E), -c)} : Set (E × ℝ)) ⊆ {(0, c)} ∪ {(0, -c)}) 3
    have hpcomp : T ≫ rp = homologyMap (integralRelativeRestriction hQp) 3 := by
      change homologyMap (integralRelativeRestriction _) 3 ≫
        homologyMap (integralRelativeRestriction _) 3 = _
      rw [← homologyMap_comp, integralRelativeRestriction_comp]
    have hmcomp : T ≫ rm = homologyMap (integralRelativeRestriction hQm) 3 := by
      change homologyMap (integralRelativeRestriction _) 3 ≫
        homologyMap (integralRelativeRestriction _) 3 = _
      rw [← homologyMap_comp, integralRelativeRestriction_comp]
    change Even ((T ≫ rp) a) ↔ Even ((T ≫ rm) a)
    rw [hpcomp, hmcomp]
    exact hpar
  have hlocal : Even (integralTripleBoundary AV LV hLVA 2 b) :=
    (even_tripleBoundary_openEmbedding_iff g hg hLVA subset_union_right
      (fun _ => Iff.rfl) (fun _ => Iff.rfl) hK.isClosed hgKr Subset.rfl 2 b).mp hmodel
  have hglobal := (even_tripleBoundary_openEmbedding_iff f hf hLVA hLA hfA hfL
    hKX.isClosed hfKr Subset.rfl 2 b).mpr hlocal
  change Even (integralTripleBoundary A L hLA 2 (F b)) at hglobal
  rw [hb] at hglobal
  have hxK : S.sphere x0 ∈ KX := by
    refine ⟨0, ⟨h0D, neg_nonpos.mpr hr.le, hr.le⟩, ?_⟩
    rw [← he0, e.left_inv hx0]
  let sx : range S.sphere := ⟨S.sphere x0, mem_range_self x0⟩
  have hj := surfaceInclusion_chartCylinder_homology_isIso S0 e hslice D hD r hr hKt 2
  exact sphere_tripleBoundary_restriction_not_even S hSA hLA sx (fun hz => hz hxK)
    alpha halpha hj hglobal

end PoincareConjecture.Proofs.M53
