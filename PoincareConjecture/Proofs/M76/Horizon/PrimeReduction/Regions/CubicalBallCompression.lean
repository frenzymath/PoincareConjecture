import PoincareConjecture.Proofs.M76.Mathlib.CubeShellHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLGluing

set_option autoImplicit false
open Set Geometry
namespace CubeShell

theorem exists_ball_dilation {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∃ H : shell 0 a ≃ₜ shell 0 c, H.IsFinitePL ∧
      ∀ x : shell 0 a, (H x : Ambient) = (c / a) • (x : Ambient) := by
  classical
  obtain ⟨K,hK,hKs⟩ := exists_finite_shell_complex 0 ha
  let L : Ambient →ᴬ[ℝ] Ambient := (c / a) • ContinuousAffineMap.id ℝ Ambient
  have hL : FinitePiecewiseAffineOn L (shell 0 a) :=
    ⟨K,hK,hKs,K.affineOnFaces_affine L⟩
  have hLi : InjOn L (shell 0 a) :=
    (smul_right_injective Ambient (div_pos hc ha).ne').injOn
  have hn (x : Ambient) : ‖L x‖ = c / a * ‖x‖ := by
    change ‖(c/a) • x‖ = _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hc ha)]
  have him : L '' shell 0 a = shell 0 c := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨norm_nonneg _,?_⟩
      rw [hn]
      calc
        c / a * ‖x‖ ≤ c / a * a := mul_le_mul_of_nonneg_left hx.2 (div_pos hc ha).le
        _ = c := div_mul_cancel₀ _ ha.ne'
    · intro hy
      refine ⟨(a/c) • y,⟨norm_nonneg _,?_⟩,?_⟩
      · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos ha hc)]
        calc
          a / c * ‖y‖ ≤ a / c * c := mul_le_mul_of_nonneg_left hy.2 (div_pos ha hc).le
          _ = a := div_mul_cancel₀ _ hc.ne'
      · change (c/a) • ((a/c) • y) = y
        rw [smul_smul]
        have hr : c/a*(a/c) = 1 := by field_simp
        rw [hr,one_smul]
  obtain ⟨H,hH,hHval⟩ := hL.exists_homeomorph_image hLi
  exact ⟨H.trans (Homeomorph.setCongr him),hH.setCongr rfl him, hHval⟩

theorem exists_boundary_fixed_ball_compression {a b c : ℝ}
    (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hcb : c < b) :
    ∃ H : shell 0 b ≃ₜ shell 0 b, H.IsFinitePL ∧
      (∀ x : shell 0 b, ‖(x : Ambient)‖ ≤ a →
        (H x : Ambient) = (c/a) • (x : Ambient)) ∧
      (∀ x : shell 0 b, ‖(x : Ambient)‖ = b → H x = x) ∧
      ∀ x : shell 0 b, ‖(x : Ambient)‖ ≤ a ↔ ‖(H x : Ambient)‖ ≤ c := by
  classical
  obtain ⟨D,hD,hDval⟩ := exists_ball_dilation ha hc
  obtain ⟨S,hS,hSval⟩ := exists_radius_homeomorph ha hab hc hcb
  have hunion {r : ℝ} (hrb : r < b) : shell 0 r ∪ shell r b = shell 0 b := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact ⟨hx.1,hx.2.trans hrb.le⟩
      · exact ⟨norm_nonneg _,hx.2⟩
    · intro hx
      by_cases hxr : ‖x‖ ≤ r
      · exact Or.inl ⟨hx.1,hxr⟩
      · exact Or.inr ⟨(lt_of_not_ge hxr).le,hx.2⟩
  obtain ⟨K,hK,hKs⟩ := exists_finite_shell_complex 0 (ha.trans hab)
  have hoverlap (x : shell 0 a) : (x : Ambient) ∈ shell a b ↔ (D x : Ambient) ∈ shell c b := by
    have hn : ‖(D x : Ambient)‖ = c/a*‖(x : Ambient)‖ := by
      rw [hDval,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hc ha)]
    constructor
    · intro hx
      have hxnorm : ‖(x : Ambient)‖ = a := le_antisymm x.property.2 hx.1
      have hn' : ‖(D x : Ambient)‖ = c := by rw [hn,hxnorm,div_mul_cancel₀ _ ha.ne']
      exact ⟨hn'.ge,hn'.le.trans hcb.le⟩
    · intro hx
      refine ⟨?_,x.property.2.trans hab.le⟩
      have hh : c/a*a ≤ c/a*‖(x : Ambient)‖ := by
        rw [div_mul_cancel₀ _ ha.ne',←hn]
        exact hx.1
      nlinarith [div_pos hc ha]
  have hagree (x : Ambient) (hx : x ∈ shell 0 a) (hs : x ∈ shell a b) :
      (D ⟨x,hx⟩ : Ambient) = S ⟨x,hs⟩ := by
    rw [hDval,(hSval ⟨x,hs⟩).2.1 (le_antisymm hx.2 hs.1)]
  obtain ⟨G,hG,hGD,hGS⟩ := Homeomorph.exists_union_of_isFinitePL D S hD hS K hK
    (hKs.trans (hunion hab).symm) hoverlap hagree
  let H := (Homeomorph.setCongr (hunion hab).symm).trans
    (G.trans (Homeomorph.setCongr (hunion hcb)))
  have hH : H.IsFinitePL := hG.setCongr (hunion hab) (hunion hcb)
  have hsmall (x : shell 0 b) (hx : ‖(x : Ambient)‖ ≤ a) :
      (H x : Ambient) = (c/a) • (x : Ambient) :=
    (hGD ⟨x,⟨norm_nonneg _,hx⟩⟩).trans (hDval _)
  refine ⟨H,hH,hsmall,?_,?_⟩
  · intro x hx
    apply Subtype.ext
    have hs : (x : Ambient) ∈ shell a b := ⟨by rw [hx]; exact hab.le,x.property.2⟩
    change (G ⟨x,_⟩ : Ambient) = x
    rw [hGS ⟨x,hs⟩,(hSval ⟨x,hs⟩).2.2 hx,div_self (ha.trans hab).ne',one_smul]
  · intro x
    constructor
    · intro hx
      have hh := (D ⟨x,⟨norm_nonneg _,hx⟩⟩).property.2
      rwa [hDval,←hsmall x hx] at hh
    · intro hx
      by_contra hxa
      have hs : (x : Ambient) ∈ shell a b := ⟨(lt_of_not_ge hxa).le,x.property.2⟩
      have heq : (H x : Ambient) = S ⟨x,hs⟩ := hGS ⟨x,hs⟩
      have hc' : c < ‖(H x : Ambient)‖ := by
        rw [heq,(hSval ⟨x,hs⟩).1]
        have hm := SquareShell.strictMono_radiusMap hab hcb (lt_of_not_ge hxa)
        rwa [(SquareShell.radiusMap_endpoints (c := c) (d := b) hab).1] at hm
      exact (not_lt_of_ge hx) hc'

end CubeShell
