import PoincareConjecture.Proofs.M38.ProjectivePolarCover
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

open Set Topology

namespace PoincareConjecture.M38

def cylinderIntegerTranslation (n : ℤ) : RoundCylinderSpace ≃ₜ RoundCylinderSpace where
  toFun p := (p.1, p.2 + n)
  invFun p := (p.1, p.2 - n)
  left_inv _p := Prod.ext rfl (add_sub_cancel_right _ _)
  right_inv _p := Prod.ext rfl (sub_add_cancel _ _)
  continuous_toFun := continuous_fst.prodMk (continuous_snd.add continuous_const)
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub continuous_const)

noncomputable def cylinderIntegerReflection (n : ℤ) : RoundCylinderSpace ≃ₜ RoundCylinderSpace where
  toFun p := (-p.1, (n : ℝ) - p.2)
  invFun p := (-p.1, (n : ℝ) - p.2)
  left_inv _p := Prod.ext (neg_neg _) (sub_sub_cancel _ _)
  right_inv _p := Prod.ext (neg_neg _) (sub_sub_cancel _ _)
  continuous_toFun := (continuous_neg.comp continuous_fst).prodMk
    (continuous_const.sub continuous_snd)
  continuous_invFun := (continuous_neg.comp continuous_fst).prodMk
    (continuous_const.sub continuous_snd)

theorem componentIn_map_subset_of_meets
    {A : Type*} [TopologicalSpace A] {V : Set A} {a : A}
    (f : A → A) (hf : Continuous f) (hV : MapsTo f V V)
    {x : A} (hx : x ∈ connectedComponentIn V a)
    (hfx : f x ∈ connectedComponentIn V a) :
    f '' connectedComponentIn V a ⊆ connectedComponentIn V a := by
  have hs : f '' connectedComponentIn V a ⊆ V := by
    rintro _ ⟨y, hy, rfl⟩
    exact hV (connectedComponentIn_subset V a hy)
  have hc : IsPreconnected (f '' connectedComponentIn V a) :=
    isPreconnected_connectedComponentIn.image f hf.continuousOn
  exact (hc.subset_connectedComponentIn (mem_image_of_mem f hx) hs).trans_eq
    (connectedComponentIn_eq hfx).symm

theorem cylinder_precompact_translation_eq_zero
    {C : Set RoundCylinderSpace} (hC : IsCompact (closure C)) (hne : C.Nonempty)
    (n : ℤ) (hstable : cylinderIntegerTranslation n '' C ⊆ C) : n = 0 := by
  have hclosure : cylinderIntegerTranslation n '' closure C ⊆ closure C :=
    (image_closure_subset_closure_image (cylinderIntegerTranslation n).continuous).trans
      (closure_mono hstable)
  obtain ⟨a, ha⟩ := hne
  obtain ⟨p, hp, hmax⟩ := hC.exists_isMaxOn ⟨a, subset_closure ha⟩ continuous_snd.continuousOn
  obtain ⟨q, hq, hmin⟩ := hC.exists_isMinOn ⟨a, subset_closure ha⟩ continuous_snd.continuousOn
  have hle := hmax (hclosure (mem_image_of_mem _ hp))
  have hge := hmin (hclosure (mem_image_of_mem _ hq))
  change p.2 + (n : ℝ) ≤ p.2 at hle
  change q.2 ≤ q.2 + (n : ℝ) at hge
  have hn : (n : ℝ) = 0 := by linarith
  exact_mod_cast hn

theorem dihedral_precompact_component_fibers
    {Q : Type*} (q : RoundCylinderSpace → Q)
    (hfibers : ∀ x y, q x = q y ↔
      ∃ n : ℤ, x = cylinderIntegerTranslation n y ∨ x = cylinderIntegerReflection n y)
    (U : Set Q) (a : RoundCylinderSpace)
    (hcompact : IsCompact (closure (connectedComponentIn (q ⁻¹' U) a))) :
    InjOn q (connectedComponentIn (q ⁻¹' U) a) ∨
      ∃ n : ℤ,
        cylinderIntegerReflection n '' connectedComponentIn (q ⁻¹' U) a =
          connectedComponentIn (q ⁻¹' U) a ∧
        ∀ x ∈ connectedComponentIn (q ⁻¹' U) a,
          ∀ y ∈ connectedComponentIn (q ⁻¹' U) a,
            q x = q y ↔ x = y ∨ x = cylinderIntegerReflection n y := by
  classical
  let C := connectedComponentIn (q ⁻¹' U) a
  have hτ (n : ℤ) (p : RoundCylinderSpace) : q (cylinderIntegerTranslation n p) = q p :=
    (hfibers _ _).mpr ⟨n, Or.inl rfl⟩
  have hρ (n : ℤ) (p : RoundCylinderSpace) : q (cylinderIntegerReflection n p) = q p :=
    (hfibers _ _).mpr ⟨n, Or.inr rfl⟩
  have htrans (n : ℤ) {p : RoundCylinderSpace} (hp : p ∈ C)
      (hpn : cylinderIntegerTranslation n p ∈ C) : n = 0 := by
    apply cylinder_precompact_translation_eq_zero hcompact ⟨p, hp⟩ n
    exact componentIn_map_subset_of_meets _ (cylinderIntegerTranslation n).continuous
      (fun y hy => by change q (cylinderIntegerTranslation n y) ∈ U; rw [hτ]; exact hy) hp hpn
  by_cases hinj : InjOn q C
  · exact Or.inl hinj
  · right
    simp only [InjOn] at hinj
    push Not at hinj
    obtain ⟨x, hx, y, hy, hxy, hne⟩ := hinj
    obtain ⟨n, hn | hn⟩ := (hfibers x y).mp hxy
    · have hn0 : n = 0 := htrans n hy (hn ▸ hx)
      have he : x = y := by
        rw [hn0] at hn
        change x = (y.1, y.2 + ((0 : ℤ) : ℝ)) at hn
        simpa only [Int.cast_zero, add_zero] using hn
      exact False.elim (hne he)
    · have hstable : cylinderIntegerReflection n '' C ⊆ C :=
        componentIn_map_subset_of_meets _ (cylinderIntegerReflection n).continuous
          (fun z hz => by change q (cylinderIntegerReflection n z) ∈ U; rw [hρ]; exact hz) hy (hn ▸ hx)
      have heq : cylinderIntegerReflection n '' C = C := by
        apply subset_antisymm hstable
        intro z hz
        refine ⟨cylinderIntegerReflection n z, hstable (mem_image_of_mem _ hz), ?_⟩
        exact (cylinderIntegerReflection n).apply_symm_apply z
      refine ⟨n, heq, ?_⟩
      intro z hz w hw
      constructor
      · intro hzw
        obtain ⟨m, hm | hm⟩ := (hfibers z w).mp hzw
        · have hm0 : m = 0 := htrans m hw (hm ▸ hz)
          apply Or.inl
          rw [hm0] at hm
          change z = (w.1, w.2 + ((0 : ℤ) : ℝ)) at hm
          simpa only [Int.cast_zero, add_zero] using hm
        · have hρz : cylinderIntegerReflection n z ∈ C := hstable (mem_image_of_mem _ hz)
          have hcomp : cylinderIntegerReflection n z = cylinderIntegerTranslation (n - m) w := by
            rw [hm]
            apply Prod.ext
            · exact neg_neg w.1
            · change (n : ℝ) - ((m : ℝ) - w.2) = w.2 + ((n - m : ℤ) : ℝ)
              rw [Int.cast_sub]
              ring
          have hnm : n - m = 0 := htrans (n - m) hw (hcomp ▸ hρz)
          have hmn : m = n := (sub_eq_zero.mp hnm).symm
          exact Or.inr (hm.trans (congrArg (fun k => cylinderIntegerReflection k w) hmn))
      · rintro (rfl | rfl)
        · rfl
        · exact hρ n w

end PoincareConjecture.M38
