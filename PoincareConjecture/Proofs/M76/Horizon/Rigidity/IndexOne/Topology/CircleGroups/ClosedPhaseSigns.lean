import PoincareConjecture.Proofs.M76.Wall.Mathlib.PLLocalSignComposition
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Euclidean.PositiveTransition
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Euclidean.Antipodal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Local.Gluing
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse
import PoincareConjecture.Proofs.M76.Wall.Mathlib.PLAtlasTransitionSigns
import PoincareConjecture.Proofs.M76.Wall.Mathlib.PLAtlasSignCover
import Mathlib.Analysis.Calculus.FDeriv.Affine

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Geometry
open scoped Topology

universe u

namespace Poincare.Topology.Orientation.ProjectivePlane

theorem positivePLOpenPartialOrientation
    (O : LocalOrientation E3) (c : OpenPartialHomeomorph E3 E3)
    (hc : c ∈ piecewiseAffineGroupoid E3) [LocallyCompactSpace c.source]
    (x : c.source) (hpositive : plLocalSign c hc x = 1) :
    (O.pullback (⟨c.source.domRestrict c, c.continuousOn.domRestrict⟩ : C(c.source, E3))
      c.isOpenEmbedding_restrict).atPoint x =
      (O.pullback (⟨Subtype.val, continuous_subtype_val⟩ : C(c.source, E3))
        c.open_source.isOpenEmbedding_subtypeVal).atPoint x := by
  classical
  let P := O.pullback
    (⟨c.source.domRestrict c, c.continuousOn.domRestrict⟩ : C(c.source, E3))
    c.isOpenEmbedding_restrict
  let Q := O.pullback (⟨Subtype.val, continuous_subtype_val⟩ : C(c.source, E3))
    c.open_source.isOpenEmbedding_subtypeVal
  obtain ⟨U, hU, hxU, hconst⟩ :=
    (IsLocallyConstant.iff_exists_open _).mp (P.comparison_locallyConstant Q) x
  obtain ⟨K, hK, hxK, hKs, hf, _, _⟩ :=
    exists_finite_paired_facet_orientation c hc x.property
  have hOU : IsOpen ((Subtype.val : c.source → E3) '' U) :=
    c.open_source.isOpenMap_subtype_val U hU
  have hxOU : (x : E3) ∈ (Subtype.val : c.source → E3) '' U := ⟨x, hxU, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((hOU.inter isOpen_interior).mem_nhds ⟨hxOU, hxK⟩)
  have hballK : ball (x : E3) r ⊆ K.space := fun _ hy => interior_subset (hball hy).2
  obtain ⟨t, ht, htc, hxt⟩ := K.exists_full_face_of_mem_interior hK hxK
  obtain ⟨y, hyt, hyball⟩ :=
    (convex_convexHull ℝ (t : Set E3)).intrinsicInterior_inter_open_nonempty
      isOpen_ball ⟨x, hxt, mem_ball_self hr⟩
  let b := (K.indep ht).affineBasisOfCard htc
  have hyint : y ∈ interior (convexHull ℝ (t : Set E3)) := by
    have h := b.mem_interior_convexHull_of_mem_intrinsicInterior (by simpa [b] using hyt)
    simpa [b] using h
  obtain ⟨A, hA⟩ := hf t ht
  have hdet : 0 < LinearMap.det A.toAffineMap.linear := by
    apply sign_eq_one_iff.mp
    exact (plLocalSign_eq_of_active_face c hc K hK hKs hf isOpen_ball
      (convex_ball (x : E3) r) hballK x (mem_ball_self hr)
      ⟨t, ht, htc, x, hxt, mem_ball_self hr⟩ A hA).symm.trans hpositive
  have hderiv : fderiv ℝ (fun z : E3 => c z) y = A.contLinear := by
    apply HasFDerivAt.fderiv
    apply A.hasFDerivAt.congr_of_eventuallyEq
    filter_upwards [isOpen_interior.mem_nhds hyint] with z hz
    exact hA (interior_subset hz)
  let y' : c.source := ⟨y, hKs (hballK hyball)⟩
  have hy : P.atPoint y' = Q.atPoint y' :=
    positiveOpenPartialOrientation O c y' (by
      change 0 < (fderiv ℝ (fun z : E3 => c z) y).toLinearMap.det
      rw [hderiv]
      exact hdet)
  have hyU : y' ∈ U := by
    obtain ⟨z, hz, heq⟩ := (hball hyball).1
    exact (Subtype.ext heq : z = y') ▸ hz
  have hcomp := hconst y' hyU
  have hyone : (Q.basis y').symm (P.atPoint y') = 1 := by
    rw [hy, ← Q.basis_one y', LinearEquiv.symm_apply_apply]
  rw [hyone] at hcomp
  have heq := congrArg (Q.basis x) hcomp.symm
  simpa only [LinearEquiv.apply_symm_apply, LocalOrientation.basis_one] using heq

theorem negativePLOpenPartialOrientation
    (O : LocalOrientation E3) (c : OpenPartialHomeomorph E3 E3)
    (hc : c ∈ piecewiseAffineGroupoid E3) [LocallyCompactSpace c.source]
    (x : c.source) (hnegative : plLocalSign c hc x = -1) :
    (O.pullback (⟨c.source.domRestrict c, c.continuousOn.domRestrict⟩ : C(c.source, E3))
      c.isOpenEmbedding_restrict).atPoint x =
      -(O.pullback (⟨Subtype.val, continuous_subtype_val⟩ : C(c.source, E3))
        c.open_source.isOpenEmbedding_subtypeVal).atPoint x := by
  let d := c.transHomeomorph (Homeomorph.neg E3)
  let negA : E3 →ᴬ[ℝ] E3 := -ContinuousAffineMap.id ℝ E3
  have hd : d ∈ piecewiseAffineGroupoid E3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward d).mpr
    have h := (locallyPiecewiseAffineOn_affine negA isOpen_univ).comp hc.1
    exact h.mono d.open_source (fun _ hz => ⟨hz, mem_univ _⟩)
  have hpos : plLocalSign d hd x = 1 := by
    obtain ⟨A, hA⟩ := exists_plAffineWitness c hc x.property
    have hsign := (plLocalSign_eq_of_witness c hc x hA).symm.trans hnegative
    have hdet : LinearMap.det A.toAffineMap.linear < 0 := sign_eq_neg_one_iff.mp hsign
    obtain ⟨K, hK, hxK, hKs, hf, t, ht, htc, hxt, hAt⟩ := hA
    have hD : IsPLAffineWitness d x (-A) :=
      ⟨K, hK, hxK, hKs, hf.postcomp negA, t, ht, htc, hxt,
        fun z hz => congrArg Neg.neg (hAt hz)⟩
    rw [plLocalSign_eq_of_witness d hd x hD]
    apply sign_eq_one_iff.mpr
    change 0 < LinearMap.det (-A.toAffineMap.linear)
    rw [← neg_one_smul ℝ A.toAffineMap.linear, LinearMap.det_smul]
    norm_num [E3, finrank_euclideanSpace]
    exact hdet
  let : LocallyCompactSpace d.source := d.open_source.locallyCompactSpace
  have hposO := positivePLOpenPartialOrientation O d hd x hpos
  let f : C(c.source, E3) := ⟨c.source.domRestrict c, c.continuousOn.domRestrict⟩
  have hcomp := LocalOrientation.pullback_comp O f negation c.isOpenEmbedding_restrict
    (Homeomorph.neg E3).isOpenEmbedding x
  have hneg := LocalOrientation.pullback_smul
    (O.pullback negation (Homeomorph.neg E3).isOpenEmbedding) O (-1)
    (fun y => by simpa only [neg_one_zsmul] using negation_pullback O y)
    f c.isOpenEmbedding_restrict x
  have heq := hneg.symm.trans (hcomp.trans hposO)
  convert (congrArg Neg.neg heq) using 1 <;>
    simp only [f, d, neg_one_zsmul, neg_neg]
  rfl

namespace LocalOrientation

theorem comparison_eq_one_or_neg_one
    {X : Type*} [TopologicalSpace X] (O P : LocalOrientation X) (x : X) :
    (P.basis x).symm (O.atPoint x) = 1 ∨
      (P.basis x).symm (O.atPoint x) = -1 := by
  let e : ℤ ≃ₗ[ℤ] ℤ := (O.basis x).trans (P.basis x).symm
  have hmul : e 1 * e.symm 1 = 1 := by
    have h := e.apply_symm_apply 1
    rw [show e.symm 1 = e.symm 1 • (1 : ℤ) by simp, map_smul] at h
    simpa only [smul_eq_mul, mul_comm] using h
  simpa only [e, LinearEquiv.trans_apply, basis_one] using
    Int.eq_one_or_neg_one_of_mul_eq_one hmul

theorem comparison_pullback
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [LocallyCompactSpace X]
    (O P : LocalOrientation Y) (f : C(X, Y))
    (hf : _root_.Topology.IsOpenEmbedding f) (x : X) :
    ((P.pullback f hf).basis x).symm ((O.pullback f hf).atPoint x) =
      (P.basis (f x)).symm (O.atPoint (f x)) := by
  apply ((P.pullback f hf).basis x).injective
  rw [LinearEquiv.apply_symm_apply, basis_apply]
  apply (localHomologyEquiv f hf x 3).injective
  change localHomologyMap f hf.injective x 3 _ =
    localHomologyMap f hf.injective x 3 _
  rw [map_zsmul, map_pullback, map_pullback, ← basis_apply,
    LinearEquiv.apply_symm_apply]

theorem pullback_smul_at
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [LocallyCompactSpace X]
    (O P : LocalOrientation Y) (a : ℤ) (f : C(X, Y))
    (hf : _root_.Topology.IsOpenEmbedding f) (x : X)
    (h : O.atPoint (f x) = a • P.atPoint (f x)) :
    (O.pullback f hf).atPoint x = a • (P.pullback f hf).atPoint x := by
  apply (localHomologyEquiv f hf x 3).injective
  change localHomologyMap f hf.injective x 3 _ =
    localHomologyMap f hf.injective x 3 _
  rw [map_zsmul, map_pullback, map_pullback, h]

end LocalOrientation

theorem plOpenPartialOrientation
    (O : LocalOrientation E3) (c : OpenPartialHomeomorph E3 E3)
    (hc : c ∈ piecewiseAffineGroupoid E3) [LocallyCompactSpace c.source]
    (x : c.source) :
    (O.pullback (⟨c.source.domRestrict c, c.continuousOn.domRestrict⟩ : C(c.source, E3))
      c.isOpenEmbedding_restrict).atPoint x =
      (plLocalSign c hc x : ℤ) •
      (O.pullback (⟨Subtype.val, continuous_subtype_val⟩ : C(c.source, E3))
        c.open_source.isOpenEmbedding_subtypeVal).atPoint x := by
  have hn := plLocalSign_ne_zero c hc x
  cases hs : plLocalSign c hc x with
  | zero => exact (hn hs).elim
  | pos => simpa using positivePLOpenPartialOrientation O c hc x hs
  | neg => simpa using negativePLOpenPartialOrientation O c hc x hs

theorem plOrientation_of_coordinate_factorization
    {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (O : LocalOrientation E3) (c : OpenPartialHomeomorph E3 E3)
    (hc : c ∈ piecewiseAffineGroupoid E3)
    (f g : C(X, E3)) (hf : _root_.Topology.IsOpenEmbedding f)
    (hg : _root_.Topology.IsOpenEmbedding g)
    (q : C(X, c.source)) (hq : _root_.Topology.IsOpenEmbedding q)
    (hsource : (⟨Subtype.val, continuous_subtype_val⟩ : C(c.source, E3)).comp q = f)
    (hfactor : (⟨c.source.domRestrict c, c.continuousOn.domRestrict⟩ :
      C(c.source, E3)).comp q = g) (x : X) :
    (O.pullback g hg).atPoint x = (plLocalSign c hc (q x) : ℤ) •
      (O.pullback f hf).atPoint x := by
  let : LocallyCompactSpace c.source := c.open_source.locallyCompactSpace
  let ci : C(c.source, E3) := ⟨Subtype.val, continuous_subtype_val⟩
  let cm : C(c.source, E3) := ⟨c.source.domRestrict c, c.continuousOn.domRestrict⟩
  have ha := LocalOrientation.pullback_smul_at
    (O.pullback cm c.isOpenEmbedding_restrict)
    (O.pullback ci c.open_source.isOpenEmbedding_subtypeVal)
    (plLocalSign c hc (q x) : ℤ) q hq x (plOpenPartialOrientation O c hc (q x))
  rw [LocalOrientation.pullback_comp, LocalOrientation.pullback_comp] at ha
  exact (LocalOrientation.pullback_congr O g (cm.comp q) hg
    (c.isOpenEmbedding_restrict.comp hq) hfactor.symm x).trans
    (ha.trans (congrArg ((plLocalSign c hc (q x) : ℤ) • ·)
      (LocalOrientation.pullback_congr O (ci.comp q) f
        (c.open_source.isOpenEmbedding_subtypeVal.comp hq) hf hsource x)))

noncomputable def chartOrientationComparison
    {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (P : LocalOrientation X) (O : LocalOrientation E3)
    (c : OpenPartialHomeomorph X E3) : LocallyConstant c.source ℤ := by
  let : LocallyCompactSpace c.source := c.open_source.locallyCompactSpace
  let A := P.pullback (⟨Subtype.val, continuous_subtype_val⟩ : C(c.source, X))
    c.open_source.isOpenEmbedding_subtypeVal
  let B := O.pullback (⟨c.source.domRestrict c, c.continuousOn.domRestrict⟩ : C(c.source, E3))
    c.isOpenEmbedding_restrict
  exact ⟨fun x => (B.basis x).symm (A.atPoint x), A.comparison_locallyConstant B⟩

theorem chartOrientationComparison_eq_one_or_neg_one
    {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (P : LocalOrientation X) (O : LocalOrientation E3)
    (c : OpenPartialHomeomorph X E3) (x : c.source) :
    chartOrientationComparison P O c x = 1 ∨
      chartOrientationComparison P O c x = -1 := by
  exact LocalOrientation.comparison_eq_one_or_neg_one _ _ x

theorem chartOrientationComparison_transition
    {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (P : LocalOrientation X) (O : LocalOrientation E3)
    (c d : OpenPartialHomeomorph X E3)
    (hcd : c.symm.trans d ∈ piecewiseAffineGroupoid E3)
    (x : X) (hc : x ∈ c.source) (hd : x ∈ d.source) :
    chartOrientationComparison P O d ⟨x, hd⟩ =
      (plLocalSign (c.symm.trans d) hcd
        ⟨c x, c.map_source hc, by
          change c.symm (c x) ∈ d.source
          rw [c.left_inv hc]
          exact hd⟩ : ℤ) *
      chartOrientationComparison P O c ⟨x, hc⟩ := by
  let W := c.source ∩ d.source
  have hW : IsOpen W := c.open_source.inter d.open_source
  let : LocallyCompactSpace W := hW.locallyCompactSpace
  let : LocallyCompactSpace c.source := c.open_source.locallyCompactSpace
  let : LocallyCompactSpace d.source := d.open_source.locallyCompactSpace
  let z : W := ⟨x, hc, hd⟩
  let wi : C(W, c.source) := ⟨fun w => ⟨w.val, w.property.1⟩,
    continuous_subtype_val.subtype_mk _⟩
  let wj : C(W, d.source) := ⟨fun w => ⟨w.val, w.property.2⟩,
    continuous_subtype_val.subtype_mk _⟩
  have hwi : _root_.Topology.IsOpenEmbedding wi := by
    apply c.open_source.isOpenEmbedding_subtypeVal.of_comp wi
    exact hW.isOpenEmbedding_subtypeVal
  have hwj : _root_.Topology.IsOpenEmbedding wj := by
    apply d.open_source.isOpenEmbedding_subtypeVal.of_comp wj
    exact hW.isOpenEmbedding_subtypeVal
  let ci : C(c.source, E3) := ⟨c.source.domRestrict c, c.continuousOn.domRestrict⟩
  let cj : C(d.source, E3) := ⟨d.source.domRestrict d, d.continuousOn.domRestrict⟩
  let ii : C(c.source, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let ij : C(d.source, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let Qi := O.pullback (ci.comp wi) (c.isOpenEmbedding_restrict.comp hwi)
  let Qj := O.pullback (cj.comp wj) (d.isOpenEmbedding_restrict.comp hwj)
  let A := P.pullback (ii.comp wi) (c.open_source.isOpenEmbedding_subtypeVal.comp hwi)
  let li := chartOrientationComparison P O c ⟨x, hc⟩
  let lj := chartOrientationComparison P O d ⟨x, hd⟩
  have hi : A.atPoint z = li • Qi.atPoint z := by
    have h := LocalOrientation.pullback_smul_at
      (P.pullback ii c.open_source.isOpenEmbedding_subtypeVal)
      (O.pullback ci c.isOpenEmbedding_restrict) li wi hwi z
      (by
        rw [← LocalOrientation.basis_apply]
        exact (((O.pullback ci c.isOpenEmbedding_restrict).basis ⟨x, hc⟩).apply_symm_apply _).symm)
    simpa only [LocalOrientation.pullback_comp] using h
  have hj : A.atPoint z = lj • Qj.atPoint z := by
    have h := LocalOrientation.pullback_smul_at
      (P.pullback ij d.open_source.isOpenEmbedding_subtypeVal)
      (O.pullback cj d.isOpenEmbedding_restrict) lj wj hwj z
      (by
        rw [← LocalOrientation.basis_apply]
        exact (((O.pullback cj d.isOpenEmbedding_restrict).basis ⟨x, hd⟩).apply_symm_apply _).symm)
    simp only [LocalOrientation.pullback_comp] at h
    convert h using 1
    rfl
  let t := c.symm.trans d
  have hqmem (w : W) : c w.val ∈ t.source := by
    refine ⟨c.map_source w.property.1, ?_⟩
    change c.symm (c w.val) ∈ d.source
    rw [c.left_inv w.property.1]
    exact w.property.2
  let q : C(W, t.source) := ⟨fun w => ⟨c w.val, hqmem w⟩,
    (ci.continuous.comp wi.continuous).subtype_mk _⟩
  have hq : _root_.Topology.IsOpenEmbedding q := by
    apply t.open_source.isOpenEmbedding_subtypeVal.of_comp q
    exact c.isOpenEmbedding_restrict.comp hwi
  let s : ℤ := plLocalSign t hcd (q z)
  have hsign : Qj.atPoint z = s • Qi.atPoint z := by
    apply plOrientation_of_coordinate_factorization O t hcd
      (ci.comp wi) (cj.comp wj) (c.isOpenEmbedding_restrict.comp hwi)
      (d.isOpenEmbedding_restrict.comp hwj) q hq rfl
    ext w : 1
    change d (c.symm (c w.val)) = d w.val
    rw [c.left_inv w.property.1]
  have heq : li = lj * s := by
    apply (Qi.basis z).injective
    rw [LocalOrientation.basis_apply, LocalOrientation.basis_apply, mul_smul]
    exact hi.symm.trans (hj.trans (congrArg (lj • ·) hsign))
  have hn := plLocalSign_ne_zero t hcd (q z)
  change lj = s * li
  cases hs : plLocalSign t hcd (q z) <;> simp_all [s]

theorem exists_plAtlas_labels_of_localOrientation
    {X : Type} {ι : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (P : LocalOrientation X) (O : LocalOrientation E3)
    (e : ι → OpenPartialHomeomorph X E3)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E3) :
    ∃ label : ∀ i, LocallyConstant (e i).source PLOrientationSheet,
      ∀ i j (x : X) (hi : x ∈ (e i).source) (hj : x ∈ (e j).source),
        (label j ⟨x, hj⟩).val =
          plAtlasTransitionSign e he i j ⟨x, hi, hj⟩ * (label i ⟨x, hi⟩).val := by
  let f (i : ι) := chartOrientationComparison P O (e i)
  have hn (i : ι) (x : (e i).source) : SignType.sign (f i x) ≠ 0 := by
    rcases chartOrientationComparison_eq_one_or_neg_one P O (e i) x with h | h <;>
      simp [f, h]
  let label (i : ι) : LocallyConstant (e i).source PLOrientationSheet :=
    ⟨fun x => ⟨SignType.sign (f i x), hn i x⟩,
      (IsLocallyConstant.iff_continuous _).mpr
        (((f i).isLocallyConstant.comp SignType.sign).continuous.subtype_mk _)⟩
  refine ⟨label, ?_⟩
  intro i j x hi hj
  have h := congrArg SignType.sign
    (chartOrientationComparison_transition P O (e i) (e j) (he i j) x hi hj)
  rw [sign_mul] at h
  have hs (s : SignType) : SignType.sign (s : ℤ) = s := by cases s <;> decide
  rw [hs] at h
  exact h

end Poincare.Topology.Orientation.ProjectivePlane
