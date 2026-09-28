import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveFiberHeight
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveMovedBand
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveMovedCollarSigns
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveSelectedCutChart
import PoincareConjecture.Proofs.M76.Mathlib.PointedCapHeightSigns












set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem AlexanderCollarSlab.exists_pointed_sign_interval
    {S s s' d b N : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β)
    (hs : IsClosed s) (hs' : IsClosed s') (hunion : s ∪ s' = S)
    (hinter : s ∩ s' ⊆ b) (hbs : b ⊆ s) (hbd : b ⊆ d)
    (hdplane : d ⊆ {x | A x = 0})
    (hsection : S ∩ {x | A x = 0} = b ∪ N)
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (p : E × ℝ).1 ∈ b → (M.chart p : E) ∈ s)
    (Ks : SimplicialComplex ℝ E) (hKs : Ks.faces.Finite) (hKss : Ks.space = s)
    {g : E → ℝ} (hg : FinitePiecewiseAffineOn g M.collar)
    (hgN : ∀ x ∈ N, g x = 0) (hgq : g q = 0)
    (hgR : ∀ x ∈ M.residual, g x = 0)
    (hgrange : ∀ x ∈ d, g x ≤ 2)
    (hgmax : ∀ x ∈ d, g x = 2 → x ∈ b)
    (hglower : ∀ x ∈ d, 0 < g x → x ∈ closure (d ∩ {y | g y < g x}))
    (hgupper : ∀ x ∈ d, g x < 2 → x ∈ closure (d ∩ {y | g x < g y}))
    (v : E) (hv : A.linear v = 1) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ t : ℝ, 0 < t → |t| < κ → ∀ H : E ≃ₜ E,
      (∀ J : SimplicialComplex ℝ E, J.faces.Finite →
        FinitePiecewiseAffineOn (H : E → E) J.space) →
      (∀ x : E, H x = x + (t * g x) • v) →
      (∀ x ∈ s, A x ≤ A (H x)) →
      (∀ x ∈ s, A x < 0 → H x = x) →
      (∀ x ∈ S, A x ∈ Ioo (0 : ℝ) β →
        x ∈ closure (S ∩ {y | A y < A x}) ∧
          x ∈ closure (S ∩ {y | A x < A y})) →
      ∀ x ∈ H '' (s ∪ d), A x ∈ Ioo (0 : ℝ) β →
        x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
          x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y}) := by
  have hsS : s ⊆ S := subset_union_left.trans hunion.subset
  have hbzero : b ⊆ {x | A x = 0} := hbd.trans hdplane
  obtain ⟨C, hC, hCval, hCA, hCroof⟩ := M.exists_selected_cut_collar_chart
    hs hs' hunion hinter hbs hbzero hselected Ks hKs hKss
  let B := s ∩ {x | A x = 0}
  have hB : B ⊆ S ∩ {x | A x = 0} := fun _ hx => ⟨hsS hx.1, hx.2⟩
  have hupper (x : E) (hx : x ∈ B) : 0 ≤ M.upper x :=
    (M.upper_bounds x (hB hx)).1
  have hCb (p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (M.upper p.1)})
      (hp : (p : E × ℝ).2 = 0) : (C p : E) = (p : E × ℝ).1 := by
    rw [hCval]
    exact M.bottom _ hp
  obtain ⟨_, ⟨J, hJ, hJs, _⟩, _⟩ := hC.symm
  have hgC : FinitePiecewiseAffineOn g (M.collar ∩ s) := by
    rw [← hJs]
    exact hg.restrict J hJ (hJs.subset.trans inter_subset_left)
  have hgroof (p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (M.upper p.1)})
      (hp : (p : E × ℝ).2 = M.upper (p : E × ℝ).1) : g (C p) = 0 :=
    hgR _ ((hCroof p).mpr hp).1
  obtain ⟨δ, hδ, hcoords⟩ := hC.exists_moved_collar_height_coordinates_with_bottom_scalar
    hupper A hCA hgC (fun p hp => congrArg g (hCb p hp)) hgroof v hv
  obtain ⟨η, hη, hstrict⟩ := M.exists_fiber_strict_height_bound hg v hv
  refine ⟨min δ η, lt_min hδ hη, fun t ht htκ H hglobal hformula hraise hneg hsource => ?_⟩
  have htδ : |t| < δ := htκ.trans_le (min_le_left _ _)
  have htη : |t| < η := htκ.trans_le (min_le_right _ _)
  have hHT : FinitePiecewiseAffineOn (H : E → E) (M.collar ∩ s) := by
    rw [← hJs]
    exact hglobal J hJ
  obtain ⟨D, _, hDA, hDroof, hDsource⟩ := hcoords t htδ H hHT (fun x _ => hformula x)
  have hfix (x : E) (hx : x ∈ M.residual) : H x = x := by
    rw [hformula, hgR x hx, mul_zero, zero_smul, add_zero]
  have hstrictC (p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (M.upper p.1)})
      (hp : 0 < (p : E × ℝ).2) : t * g (p : E × ℝ).1 < A (H (C p)) := by
    rw [hCval]
    exact (hstrict t htη H (fun x _ => hformula x) ⟨p, hB p.property.1, p.property.2⟩).2 hp
  have hcapheight (x : E) (hx : x ∈ d) : A (H x) = t * g x := by
    rw [hformula, add_comm x]
    change A ((t * g x) • v +ᵥ x) = t * g x
    rw [A.map_vadd, map_smul, hv]
    change t * g x * 1 + A x = t * g x
    rw [hdplane hx, mul_one, add_zero]
  have hbottom (p : {p : E × ℝ | p.1 ∈ B ∧
      p.2 ∈ Icc (t * g p.1) (M.upper p.1)})
      (hp : (p : E × ℝ).2 = t * g (p : E × ℝ).1)
      (hpos : 0 < A (D p)) : (D p : E) ∈ H '' d := by
    obtain ⟨z, hzbase, hzval, _⟩ := hDsource p
    have hz0 : (z : E × ℝ).2 = 0 := by
      apply le_antisymm _ z.property.2.1
      by_contra hn
      have hlt := hstrictC z (lt_of_not_ge hn)
      rw [hzbase, ← hzval, hDA p, hp] at hlt
      exact (lt_irrefl _ hlt).elim
    have hgpos : 0 < g (p : E × ℝ).1 := by
      rw [hDA p, hp] at hpos
      exact (mul_pos_iff_of_pos_left ht).mp hpos
    have hpb : (p : E × ℝ).1 ∈ b := by
      rcases hsection.subset (hB p.property.1) with h | h
      · exact h
      · exact (hgpos.ne' (hgN _ h)).elim
    refine ⟨(p : E × ℝ).1, hbd hpb, ?_⟩
    rw [hzval, hCb z hz0, hzbase]
  have hrim (x : E) (hxb : x ∈ b) (hgpos : 0 < g x) :
      ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (t * g p.1) (M.upper p.1)},
        (D p : E) = H x ∧ (p : E × ℝ).2 < M.upper (p : E × ℝ).1 := by
    have hxB : x ∈ B := ⟨hbs hxb, hbzero hxb⟩
    let z₀ : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (M.upper p.1)} :=
      ⟨(x, 0), hxB, le_rfl, hupper x hxB⟩
    have hCzero : (C z₀ : E) = x := hCb z₀ rfl
    have hxT : x ∈ M.collar ∩ s := hCzero ▸ (C z₀).property
    let p := D.symm ⟨H x, mem_image_of_mem H hxT⟩
    have hp : (D p : E) = H x := congrArg Subtype.val (D.apply_symm_apply _)
    obtain ⟨z, hzbase, hzval, _⟩ := hDsource p
    have hCz : (C z : E) = x := H.injective (hzval.symm.trans hp)
    have hz0 : (z : E × ℝ).2 = 0 :=
      (hCA z).symm.trans ((congrArg A hCz).trans (hbzero hxb))
    have hbase : (p : E × ℝ).1 = x :=
      hzbase.symm.trans ((hCb z hz0).symm.trans hCz)
    have hxq : x ≠ q := by
      intro heq
      exact hgpos.ne' ((congrArg g heq).trans hgq)
    have hxupper : 0 < M.upper x := M.upper_pos x (hB hxB) hxq
    let ztop : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (M.upper p.1)} :=
      ⟨(x, M.upper x), hxB, hxupper.le, le_rfl⟩
    have hgap : t * g x < M.upper x := by
      have h := hstrictC ztop hxupper
      rw [hfix (C ztop) ((hCroof ztop).mpr rfl).1, hCA ztop] at h
      exact h
    refine ⟨p, hp, ?_⟩
    rw [← hDA p, hp, hcapheight x (hbd hxb), hbase]
    exact hgap
  have htarget : H '' (M.collar ∩ s) ⊆ H '' (s ∪ d) :=
    image_mono (inter_subset_right.trans subset_union_left)
  have hcap := H.pointed_cap_mem_both_height_closures
    (s := s) (d := d) (b := b) (B := B) (T := H '' (M.collar ∩ s))
    (lower := fun x => t * g x) (upper := M.upper) A g ht hcapheight
    hgrange hgmax hglower hgupper D hDA htarget hrim
  exact M.mem_both_height_closures_of_capped_moved_collar
    (B := B) (lower := fun x => t * g x) (upper := M.upper) hs' hunion
    (hinter.trans hbzero) H hraise hneg hfix D hDA
    (fun p hp => by rw [hDroof p hp]; exact (hCroof _).mpr rfl)
    hbottom hsource (fun x hx hxA => hcap x hx hxA.1)

end Geometry
