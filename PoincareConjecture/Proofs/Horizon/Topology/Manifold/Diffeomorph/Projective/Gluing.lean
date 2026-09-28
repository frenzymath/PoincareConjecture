import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Models
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.RadialCylinder
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.LocalDiffeomorph

noncomputable section
set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.ProjectiveGluing

open PoincareConjecture

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem localDiffeomorphAt_of_smooth_neighborhood
    {X Y : Type*} [TopologicalSpace X] [ChartedSpace E3 X]
    [TopologicalSpace Y] [ChartedSpace E3 Y]
    (e : OpenPartialHomeomorph X Y)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {x : X} (hx : x ∈ e.source) : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ e x := by
  exact ⟨{
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := he
    contMDiffOn_invFun := hei }, hx, fun _ _ => rfl⟩

private theorem radial_representation_of_annulus {x : E3} {r : ℝ}
    (hlo : Real.exp (-r) < ‖x‖) (hhi : ‖x‖ < Real.exp r) :
    ∃ (q : UnitTwoSphere) (t : ℝ), |t| < r ∧ x = Real.exp t • (q : E3) := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp ((Real.exp_pos (-r)).trans hlo)
  let J := Poincare.sphereCylinderDiffeomorphPunctured
  let z := J.symm ⟨x, hx0⟩
  have hz : Real.exp z.2 • (z.1 : E3) = x :=
    congrArg Subtype.val (J.apply_symm_apply ⟨x, hx0⟩)
  have hn : Real.exp z.2 = ‖x‖ := by
    rw [← hz, norm_smul]
    simp [Real.norm_eq_abs, Real.abs_exp]
  exact ⟨z.1, z.2, abs_lt.mpr
    ⟨Real.exp_lt_exp.mp (hn.symm ▸ hlo), Real.exp_lt_exp.mp (hn.symm ▸ hhi)⟩, hz.symm⟩

private theorem localDiffeomorph_codRestrict
    {X M : Type*} [TopologicalSpace X] [ChartedSpace E3 X]
    [TopologicalSpace M] [ChartedSpace E3 M]
    (Y : Opens M) (f : X → M) (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f)
    (hmem : ∀ x, f x ∈ Y) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x => (⟨f x, hmem x⟩ : Y)) := by
  let k : X → Y := fun x => ⟨f x, hmem x⟩
  have hk : Continuous k := hf.contMDiff.continuous.subtype_mk _
  intro x
  have hv := Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) Y (k x)
  have hcomp := (hf x).comp (𝓡 3) Y hv.localInverse_isLocalDiffeomorphAt
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hk.continuousAt.preimage_mem_nhds
    (hv.localInverse.open_target.mem_nhds hv.localInverse_mem_target)] with z hz
  exact (hv.localInverse_left_inv hz).symm

def antipodalBallComplement (b : OpenPartialHomeomorph E3 UnitThreeSphere) :
    Set UnitThreeSphere :=
  (b '' Metric.ball 0 1 ∪ Neg.neg '' (b '' Metric.ball 0 1))ᶜ

theorem exists_smooth_cover_of_matching_ball
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    {p : RealProjectiveThree} {U : Set M}
    (S : StandardPuncturedProjectiveCover M p U)
    (a : UnitThreeSphere) (ha : Quotient.mk' a = p)
    (b : OpenPartialHomeomorph E3 UnitThreeSphere)
    (hbs : Metric.closedBall 0 1 ⊆ b.source)
    (hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source)
    (hbi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target)
    (hb0 : b 0 = a)
    (hBB : Disjoint (b '' Metric.closedBall 0 1)
      (Neg.neg '' (b '' Metric.closedBall 0 1)))
    (v : OpenPartialHomeomorph E3 M)
    (hvs : Metric.closedBall 0 1 ⊆ v.source)
    (hv : ContMDiffOn (𝓡 3) (𝓡 3) ∞ v v.source)
    (hvi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ v.symm v.target)
    {r : ℝ} (hr : 0 < r)
    (hmatch : ∀ (q : UnitTwoSphere) (t : ℝ), |t| < r →
      Real.exp t • (q : E3) ∈ b.source ∧
      Real.exp t • (q : E3) ∈ v.source ∧
      S.cover (b (Real.exp t • (q : E3))) = v (Real.exp t • (q : E3)))
    (hdisjoint : Disjoint (v '' Metric.ball 0 1)
      (S.cover '' antipodalBallComplement b))
    (Y : Opens M)
    (hY : (Y : Set M) =
      S.cover '' antipodalBallComplement b ∪ v '' Metric.closedBall 0 1) :
    ∃ P : StandardProjectiveSmoothCover Y,
      (∀ x ∈ antipodalBallComplement b, (P.cover x : M) = S.cover x) ∧
      (∀ z ∈ Metric.closedBall (0 : E3) 1, (P.cover (b z) : M) = v z) := by
  classical
  let K := antipodalBallComplement b
  let A := b '' Metric.ball 0 1
  let B := b '' Metric.closedBall 0 1
  have hB : IsClosed B := ((isCompact_closedBall (0 : E3) 1).image_of_continuousOn
    (b.continuousOn.mono hbs)).isClosed
  have hnegmem (U : Set UnitThreeSphere) (x : UnitThreeSphere) :
      x ∈ Neg.neg '' U ↔ -x ∈ U := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa only [neg_neg] using hz
    · intro hx
      exact ⟨-x, hx, neg_neg x⟩
  have hA : IsOpen A :=
    b.isOpen_image_of_subset_source Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hbs)
  have hAB : A ⊆ B := image_mono Metric.ball_subset_closedBall
  have hanti {x : UnitThreeSphere} (hx : x ∈ B) : -x ∉ B := by
    intro hn
    exact disjoint_left.mp hBB hx ((hnegmem B x).mpr hn)
  have hK (x : UnitThreeSphere) : x ∈ K ↔ x ∉ A ∧ -x ∉ A := by
    change ¬(x ∈ A ∪ Neg.neg '' A) ↔ _
    simp only [mem_union, hnegmem, not_or]
  have hnegK {x : UnitThreeSphere} (hx : x ∈ K) : -x ∈ K := by
    have h := (hK x).mp hx
    exact (hK (-x)).mpr ⟨h.2, by simpa only [neg_neg] using h.1⟩
  have haA : a ∈ A := hb0 ▸ mem_image_of_mem b (Metric.mem_ball_self (by norm_num))
  have hKpuncture {x : UnitThreeSphere} (hx : x ∈ K) : Quotient.mk' x ≠ p := by
    intro hxp
    have hxa : Quotient.mk' x = Quotient.mk' a := hxp.trans ha.symm
    rcases Quotient.exact hxa with h | h
    · exact ((hK x).mp hx).1 (h.symm ▸ haA)
    · exact ((hK x).mp hx).2 (by simpa only [h, neg_neg] using haA)
  let f : UnitThreeSphere → M := fun x =>
    if x ∈ B then v (b.symm x) else if -x ∈ B then v (b.symm (-x)) else S.cover x
  have hfB {x : UnitThreeSphere} (hx : x ∈ B) : f x = v (b.symm x) := if_pos hx
  have hfout {x : UnitThreeSphere} (hx : x ∉ B) (hnx : -x ∉ B) : f x = S.cover x := by
    simp only [f, if_neg hx, if_neg hnx]
  have hfneg (x : UnitThreeSphere) : f (-x) = f x := by
    by_cases hx : x ∈ B
    · simp only [f, if_pos hx, if_neg (hanti hx), neg_neg]
    · by_cases hnx : -x ∈ B
      · simp only [f, if_neg hx, if_pos hnx]
      · rw [hfout hx hnx, hfout hnx (by simpa only [neg_neg] using hx)]
        have hxK := (hK x).mpr ⟨fun h => hx (hAB h), fun h => hnx (hAB h)⟩
        have hnK := (hK (-x)).mpr
          ⟨fun h => hnx (hAB h), by simpa only [neg_neg] using fun h => hx (hAB h)⟩
        exact (S.fibers (-x) x (hKpuncture hnK) (hKpuncture hxK)).mpr (Or.inr rfl)
  have hfball (z : E3) (hz : z ∈ Metric.closedBall 0 1) : f (b z) = v z := by
    rw [hfB (mem_image_of_mem b hz), b.left_inv (hbs hz)]
  have hzero (q : UnitTwoSphere) : S.cover (b q) = v q := by
    simpa only [Real.exp_zero, one_smul] using (hmatch q 0 (by simpa using hr)).2.2
  have hfK : EqOn f S.cover K := by
    intro x hx
    have hside {y : UnitThreeSphere} (hyK : y ∈ K) (hyB : y ∈ B) : f y = S.cover y := by
      obtain ⟨z, hz, rfl⟩ := hyB
      have hznot : z ∉ Metric.ball (0 : E3) 1 := by
        intro h
        exact ((hK _).mp hyK).1 ((mem_image_of_mem b h))
      have hzsphere : z ∈ Metric.sphere (0 : E3) 1 :=
        Metric.closedBall_sdiff_ball.subset ⟨hz, hznot⟩
      exact (hfball z hz).trans (hzero ⟨z, hzsphere⟩).symm
    by_cases hxB : x ∈ B
    · exact hside hx hxB
    · by_cases hnxB : -x ∈ B
      · have hnxK : -x ∈ K := hnegK hx
        exact (hfneg x).symm.trans ((hside hnxK hnxB).trans
          ((S.fibers (-x) x (hKpuncture hnxK) (hKpuncture hx)).mpr (Or.inr rfl)))
      · exact hfout hxB hnxB
  have hfA {x : UnitThreeSphere} (hx : x ∈ A) : f x ∈ v '' Metric.ball 0 1 := by
    obtain ⟨z, hz, rfl⟩ := hx
    rw [hfball z (Metric.ball_subset_closedBall hz)]
    exact mem_image_of_mem v hz
  have hsame {x y : UnitThreeSphere} (hx : x ∈ A) (hy : y ∈ A)
      (hxy : f x = f y) : x = y := by
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    rw [hfball z (Metric.ball_subset_closedBall hz),
      hfball w (Metric.ball_subset_closedBall hw)] at hxy
    exact congrArg b (v.injOn (hvs (Metric.ball_subset_closedBall hz))
      (hvs (Metric.ball_subset_closedBall hw)) hxy)
  have hAfiber {x y : UnitThreeSphere} (hx : x ∈ A) (hxy : f x = f y) :
      x = y ∨ x = -y := by
    by_cases hy : y ∈ A
    · exact Or.inl (hsame hx hy hxy)
    · by_cases hny : -y ∈ A
      · exact Or.inr (hsame hx hny (hxy.trans (hfneg y).symm))
      · have hyK := (hK y).mpr ⟨hy, hny⟩
        have hycore : f y ∈ S.cover '' K :=
          (hfK hyK).symm ▸ mem_image_of_mem S.cover hyK
        exact False.elim (disjoint_left.mp hdisjoint (hxy ▸ hfA hx) hycore)
  have hfibers (x y : UnitThreeSphere) : f x = f y ↔ x = y ∨ x = -y := by
    constructor
    · intro hxy
      by_cases hx : x ∈ A
      · exact hAfiber hx hxy
      · by_cases hnx : -x ∈ A
        · rcases hAfiber hnx ((hfneg x).trans hxy) with h | h
          · exact Or.inr (by simpa only [neg_neg] using congrArg Neg.neg h)
          · exact Or.inl (by simpa only [neg_neg] using congrArg Neg.neg h)
        · have hxK := (hK x).mpr ⟨hx, hnx⟩
          by_cases hy : y ∈ A
          · rcases hAfiber hy hxy.symm with h | h
            · exact Or.inl h.symm
            · exact Or.inr (by simpa only [neg_neg] using (congrArg Neg.neg h).symm)
          · by_cases hny : -y ∈ A
            · rcases hAfiber hny ((hfneg y).trans hxy.symm) with h | h
              · exact Or.inr h.symm
              · exact Or.inl (by simpa only [neg_neg] using (congrArg Neg.neg h).symm)
            · have hyK := (hK y).mpr ⟨hy, hny⟩
              rw [hfK hxK, hfK hyK] at hxy
              exact (S.fibers x y (hKpuncture hxK) (hKpuncture hyK)).mp hxy
    · rintro (rfl | h)
      · rfl
      · rw [h, hfneg]
  have hmem (x : UnitThreeSphere) : f x ∈ Y := by
    change f x ∈ (Y : Set M)
    rw [hY]
    by_cases hx : x ∈ B
    · right
      obtain ⟨z, hz, rfl⟩ := hx
      rw [hfball z hz]
      exact mem_image_of_mem v hz
    · by_cases hnx : -x ∈ B
      · right
        obtain ⟨z, hz, heq⟩ := hnx
        rw [← hfneg x, ← heq, hfball z hz]
        exact mem_image_of_mem v hz
      · left
        have hxK := (hK x).mpr ⟨fun h => hx (hAB h), fun h => hnx (hAB h)⟩
        exact (hfK hxK).symm ▸ mem_image_of_mem S.cover hxK
  have hsurj (y : Y) : ∃ x, f x = y.val := by
    rcases hY.subset y.property with hy | hy
    · obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨x, (hfK hx).trans hxy⟩
    · obtain ⟨z, hz, heq⟩ := hy
      exact ⟨b z, (hfball z hz).trans heq⟩
  have hlocal : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f := by
    let e := b.symm.trans v
    have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source :=
      hv.comp (hbi.mono inter_subset_left) inter_subset_right
    have hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target :=
      hb.comp (hvi.mono inter_subset_left) inter_subset_right
    let L := {z : E3 | Real.exp (-r) < ‖z‖ ∧ ‖z‖ < Real.exp r}
    have hLo : IsOpen L :=
      (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
    have hLs : L ⊆ b.source := by
      intro z hz
      obtain ⟨q, t, ht, rfl⟩ := radial_representation_of_annulus hz.1 hz.2
      exact (hmatch q t ht).1
    have hLimage : IsOpen (b '' L) := b.isOpen_image_of_subset_source hLo hLs
    have hnegBo : IsOpen {y : UnitThreeSphere | -y ∉ B} :=
      hB.isOpen_compl.preimage continuous_neg
    have hlocalB {x : UnitThreeSphere} (hx : x ∈ B) :
        IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ f x := by
      obtain ⟨z, hz, rfl⟩ := hx
      have hBz : b z ∈ B := mem_image_of_mem b hz
      have hes : b z ∈ e.source := by
        refine ⟨b.map_source (hbs hz), ?_⟩
        change b.symm (b z) ∈ v.source
        rw [b.left_inv (hbs hz)]
        exact hvs hz
      apply (localDiffeomorphAt_of_smooth_neighborhood e he hei hes).congr_of_eventuallyEq
      by_cases hzb : z ∈ Metric.ball (0 : E3) 1
      · have hzA : b z ∈ A := mem_image_of_mem b hzb
        filter_upwards [hA.mem_nhds hzA] with y hy
        exact hfB (hAB hy)
      · have hzsphere : z ∈ Metric.sphere (0 : E3) 1 :=
          Metric.closedBall_sdiff_ball.subset ⟨hz, hzb⟩
        have hznorm : ‖z‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hzsphere
        have hzL : z ∈ L := by
          change Real.exp (-r) < ‖z‖ ∧ ‖z‖ < Real.exp r
          rw [hznorm]
          exact ⟨Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hr), Real.one_lt_exp_iff.mpr hr⟩
        filter_upwards [hLimage.mem_nhds (mem_image_of_mem b hzL),
          hnegBo.mem_nhds (hanti hBz)] with y hy hyn
        change f y = v (b.symm y)
        by_cases hyB : y ∈ B
        · exact hfB hyB
        · rw [hfout hyB hyn]
          obtain ⟨w, hw, rfl⟩ := hy
          obtain ⟨q, t, ht, rfl⟩ := radial_representation_of_annulus hw.1 hw.2
          rw [b.left_inv (hmatch q t ht).1]
          exact (hmatch q t ht).2.2
    intro x
    by_cases hx : x ∈ B
    · exact hlocalB hx
    · by_cases hnx : -x ∈ B
      · let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
        let J : Diffeomorph (𝓡 3) (𝓡 3) UnitThreeSphere UnitThreeSphere ∞ := {
          toEquiv := Equiv.neg UnitThreeSphere
          contMDiff_toFun := contMDiff_neg_sphere
          contMDiff_invFun := contMDiff_neg_sphere }
        apply ((J.isLocalDiffeomorph x).comp (𝓡 3) M (hlocalB hnx)).congr_of_eventuallyEq
        exact Eventually.of_forall fun y => (hfneg y).symm
      · have hxK := (hK x).mpr ⟨fun h => hx (hAB h), fun h => hnx (hAB h)⟩
        apply (S.local_diffeomorph ⟨x, hKpuncture hxK⟩).congr_of_eventuallyEq
        filter_upwards [hB.isOpen_compl.mem_nhds hx, hnegBo.mem_nhds hnx] with y hy hny
        exact hfout hy hny
  let P : StandardProjectiveSmoothCover Y := {
    cover := fun x => ⟨f x, hmem x⟩
    surjective := fun y => by
      obtain ⟨x, hx⟩ := hsurj y
      exact ⟨x, Subtype.ext hx⟩
    fibers := fun x y => by simpa only [Subtype.mk.injEq] using hfibers x y
    local_diffeomorph := localDiffeomorph_codRestrict Y f hlocal hmem }
  exact ⟨P, hfK, hfball⟩

end PoincareConjecture.ProjectiveGluing
