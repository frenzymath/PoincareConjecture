import PoincareConjecture.Proofs.M53.Prop15_12_HalfSpaceExpansion
import Mathlib.Topology.Homotopy.Equiv

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped unitInterval ContinuousMap

universe u

namespace PoincareConjecture.Proofs.M53

variable {E : Type u} [NormedAddCommGroup E]

theorem planeExterior_subset_twoPuncture
    (K : Set (E × ℝ)) (c : ℝ) (hc : 0 < c)
    (hp : ((0 : E), c) ∈ K) (hm : ((0 : E), -c) ∈ K) :
    {y : E × ℝ | y.2 = 0} ∪ Kᶜ ⊆ ({((0 : E), c)} ∪ {(0, -c)})ᶜ := by
  intro y hy hq
  rcases hq with hq | hq
  · have he : y = (0, c) := hq
    subst y
    rcases hy with hz | hy
    · exact hc.ne' hz
    · exact hy hp
  · have he : y = (0, -c) := hq
    subst y
    rcases hy with hz | hy
    · exact (neg_ne_zero.mpr hc.ne') hz
    · exact hy hm

def planeExteriorPunctureInclusion
    (K : Set (E × ℝ)) (c : ℝ) (hc : 0 < c)
    (hp : ((0 : E), c) ∈ K) (hm : ((0 : E), -c) ∈ K) :
    C(({y : E × ℝ | y.2 = 0} ∪ Kᶜ : Set (E × ℝ)),
      (({((0 : E), c)} ∪ {(0, -c)})ᶜ : Set (E × ℝ))) :=
  ⟨fun y => ⟨y.val, planeExterior_subset_twoPuncture K c hc hp hm y.property⟩,
    continuous_subtype_val.subtype_mk _⟩

variable [NormedSpace ℝ E]

def planeExteriorPunctureHomotopyEquiv
    (K : Set (E × ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (c : ℝ) (hc : 0 < c) (hp : ((0 : E), c) ∈ K) (hm : ((0 : E), -c) ∈ K) :
    ({y : E × ℝ | y.2 = 0} ∪ Kᶜ : Set (E × ℝ)) ≃ₕ
      (({((0 : E), c)} ∪ {(0, -c)})ᶜ : Set (E × ℝ)) := by
  let A : Set (E × ℝ) := {y | y.2 = 0} ∪ Kᶜ
  let Q : Set (E × ℝ) := ({((0 : E), c)} ∪ {(0, -c)})ᶜ
  let Rp := (hK.isBounded.subset_ball_lt 0 ((0 : E), c)).choose
  let Rm := (hK.isBounded.subset_ball_lt 0 ((0 : E), -c)).choose
  have hRp : 0 < Rp := (hK.isBounded.subset_ball_lt 0 ((0 : E), c)).choose_spec.1
  have hRm : 0 < Rm := (hK.isBounded.subset_ball_lt 0 ((0 : E), -c)).choose_spec.1
  have hKp : K ⊆ ball ((0 : E), c) Rp :=
    (hK.isBounded.subset_ball_lt 0 ((0 : E), c)).choose_spec.2
  have hKm : K ⊆ ball ((0 : E), -c) Rm :=
    (hK.isBounded.subset_ball_lt 0 ((0 : E), -c)).choose_spec.2
  let ep : C(Q, ({((0 : E), c)}ᶜ : Set (E × ℝ))) :=
    ⟨fun y => ⟨y.val, fun hy => y.property (Or.inl hy)⟩,
      continuous_subtype_val.subtype_mk _⟩
  let em : C(Q, ({((0 : E), -c)}ᶜ : Set (E × ℝ))) :=
    ⟨fun y => ⟨y.val, fun hy => y.property (Or.inr hy)⟩,
      continuous_subtype_val.subtype_mk _⟩
  let upper : C(unitInterval × Q, E × ℝ) :=
    ⟨fun z => halfSpaceExpansion c Rp hRp (z.1, ep z.2),
      (halfSpaceExpansion c Rp hRp).continuous.comp
        (continuous_fst.prodMk (ep.continuous.comp continuous_snd))⟩
  let lower : C(unitInterval × Q, E × ℝ) :=
    ⟨fun z => halfSpaceExpansion (-c) Rm hRm (z.1, em z.2),
      (halfSpaceExpansion (-c) Rm hRm).continuous.comp
        (continuous_fst.prodMk (em.continuous.comp continuous_snd))⟩
  let H : C(unitInterval × Q, E × ℝ) :=
    ⟨fun z => if 0 ≤ z.2.val.2 then upper z else lower z, by
      apply upper.continuous.if_le lower.continuous continuous_const
        (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))
      intro z hz
      exact (halfSpaceExpansion_plane c Rp hRp z.1 (ep z.2) hz.symm).trans
        (halfSpaceExpansion_plane (-c) Rm hRm z.1 (em z.2) hz.symm).symm⟩
  have hHQ (s : unitInterval) (y : Q) : H (s, y) ∈ Q := by
    change (if 0 ≤ y.val.2 then upper (s, y) else lower (s, y)) ∉
      {((0 : E), c)} ∪ {(0, -c)}
    split_ifs with hy
    · have hh := halfSpaceExpansion_height c Rp hc.ne' hRp s (ep y)
        (div_nonneg hy hc.le)
      rintro (hq | hq)
      · exact halfSpaceExpansion_ne_center c Rp hRp s (ep y) hq
      · have he : halfSpaceExpansion c Rp hRp (s, ep y) = (0, -c) := hq
        rw [he] at hh
        norm_num [neg_div, hc.ne'] at hh
    · have hh := halfSpaceExpansion_height (-c) Rm (neg_ne_zero.mpr hc.ne') hRm s (em y)
        (div_nonneg_of_nonpos (le_of_not_ge hy) (neg_nonpos.mpr hc.le))
      rintro (hq | hq)
      · have he : halfSpaceExpansion (-c) Rm hRm (s, em y) = (0, c) := hq
        rw [he] at hh
        norm_num [div_neg, hc.ne'] at hh
      · exact halfSpaceExpansion_ne_center (-c) Rm hRm s (em y) hq
  have hH0 (y : Q) : H (0, y) ∈ A := by
    change (if 0 ≤ y.val.2 then upper (0, y) else lower (0, y)) ∈ A
    split_ifs with hy
    · rcases halfSpaceExpansion_zero_mem c Rp hc.ne' hRp (ep y)
        (div_nonneg hy hc.le) with hz | hn
      · exact Or.inl hz
      · right
        intro hmem
        have hb := hKp hmem
        rw [mem_ball, dist_eq_norm] at hb
        exact (not_lt_of_ge hn) hb
    · rcases halfSpaceExpansion_zero_mem (-c) Rm (neg_ne_zero.mpr hc.ne') hRm (em y)
        (div_nonneg_of_nonpos (le_of_not_ge hy) (neg_nonpos.mpr hc.le)) with hz | hn
      · exact Or.inl hz
      · right
        intro hmem
        have hb := hKm hmem
        rw [mem_ball, dist_eq_norm] at hb
        exact (not_lt_of_ge hn) hb
  have hH1 (y : Q) : H (1, y) = y.val := by
    change (if 0 ≤ y.val.2 then upper (1, y) else lower (1, y)) = y.val
    split_ifs
    · exact halfSpaceExpansion_one c Rp hRp (ep y)
    · exact halfSpaceExpansion_one (-c) Rm hRm (em y)
  let i : C(A, Q) := planeExteriorPunctureInclusion K c hc hp hm
  have hHA (s : unitInterval) (y : A) : H (s, i y) ∈ A := by
    change (if 0 ≤ y.val.2 then upper (s, i y) else lower (s, i y)) ∈ A
    rcases y.property with hz | hy
    · rw [if_pos (by rw [hz])]
      left
      change (halfSpaceExpansion c Rp hRp (s, ep (i y))).2 = 0
      rw [halfSpaceExpansion_plane c Rp hRp s (ep (i y)) hz]
      exact hz
    · split_ifs
      · exact Or.inr (halfSpaceExpansion_not_mem c Rp hRp K hconv hp s (ep (i y)) hy)
      · exact Or.inr (halfSpaceExpansion_not_mem (-c) Rm hRm K hconv hm s (em (i y)) hy)
  let j : C(Q, A) :=
    ⟨fun y => ⟨H (0, y), hH0 y⟩,
      (H.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  let HA : (j.comp i).Homotopy (ContinuousMap.id A) :=
    { toFun := fun z => ⟨H (z.1, i z.2), hHA z.1 z.2⟩
      continuous_toFun := (H.continuous.comp
        (continuous_fst.prodMk (i.continuous.comp continuous_snd))).subtype_mk _
      map_zero_left _ := rfl
      map_one_left y := Subtype.ext (hH1 (i y)) }
  let HQ : (i.comp j).Homotopy (ContinuousMap.id Q) :=
    { toFun := fun z => ⟨H z, hHQ z.1 z.2⟩
      continuous_toFun := H.continuous.subtype_mk _
      map_zero_left _ := rfl
      map_one_left y := Subtype.ext (hH1 y) }
  exact ⟨i, j, ⟨HA⟩, ⟨HQ⟩⟩

theorem planeExteriorPunctureHomotopyEquiv_toFun
    (K : Set (E × ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (c : ℝ) (hc : 0 < c) (hp : ((0 : E), c) ∈ K) (hm : ((0 : E), -c) ∈ K) :
    (planeExteriorPunctureHomotopyEquiv K hK hconv c hc hp hm).toFun =
      planeExteriorPunctureInclusion K c hc hp hm := rfl

end PoincareConjecture.Proofs.M53
