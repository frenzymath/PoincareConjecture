import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.LinearAlgebra.FreeModule.PID

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v

namespace CategoryTheory.ShortComplex

variable {K : Type u} [CommRing K] {S : ShortComplex (ModuleCat.{v} K)}

theorem trace_of_splitting
    [Module.Free K S.X₁] [Module.Finite K S.X₁]
    [Module.Free K S.X₂] [Module.Finite K S.X₂]
    [Module.Free K S.X₃] [Module.Finite K S.X₃] (s : S.Splitting) (f : S ⟶ S) :
    LinearMap.trace K S.X₂ f.τ₂.hom =
      LinearMap.trace K S.X₁ f.τ₁.hom + LinearMap.trace K S.X₃ f.τ₃.hom := by
  have hsplit : f.τ₂ = (f.τ₂ ≫ s.r) ≫ S.f + (f.τ₂ ≫ S.g) ≫ s.s := by
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_add, s.id, Category.comp_id]
  have hleft : S.f ≫ f.τ₂ ≫ s.r = f.τ₁ := by
    rw [← Category.assoc, ← f.comm₁₂, Category.assoc, s.f_r, Category.comp_id]
  have hright : s.s ≫ f.τ₂ ≫ S.g = f.τ₃ := by
    rw [f.comm₂₃, ← Category.assoc, s.s_g, Category.id_comp]
  have hleftTrace := LinearMap.trace_comp_comm' (f.τ₂ ≫ s.r).hom S.f.hom
  rw [hsplit, ModuleCat.hom_add, map_add]
  congr 1
  · change LinearMap.trace K S.X₂ (S.f.hom ∘ₗ (f.τ₂ ≫ s.r).hom) = _
    rw [hleftTrace]
    change LinearMap.trace K S.X₁ (S.f ≫ f.τ₂ ≫ s.r).hom = _
    rw [hleft]
  · change LinearMap.trace K S.X₂ (s.s.hom ∘ₗ (f.τ₂ ≫ S.g).hom) = _
    rw [LinearMap.trace_comp_comm']
    change LinearMap.trace K S.X₃ (s.s ≫ f.τ₂ ≫ S.g).hom = _
    rw [hright]

theorem trace_of_shortExact
    [Module.Free K S.X₁] [Module.Finite K S.X₁]
    [Module.Free K S.X₂] [Module.Finite K S.X₂]
    [Module.Free K S.X₃] [Module.Finite K S.X₃] (hS : S.ShortExact) (f : S ⟶ S) :
    LinearMap.trace K S.X₂ f.τ₂.hom =
      LinearMap.trace K S.X₁ f.τ₁.hom + LinearMap.trace K S.X₃ f.τ₃.hom :=
  trace_of_splitting hS.splittingOfProjective f

end CategoryTheory.ShortComplex

namespace LinearMap

variable {K : Type u} [CommRing K] [IsDomain K] [IsPrincipalIdealRing K]
  {A B C D : Type v} [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [AddCommGroup D]
  [Module K A] [Module K B] [Module K C] [Module K D]

theorem trace_exact_four
    [Module.Free K A] [Module.Finite K A]
    [Module.Free K B] [Module.Finite K B]
    [Module.Free K C] [Module.Finite K C]
    [Module.Free K D] [Module.Finite K D]
    (f : A →ₗ[K] B) (g : B →ₗ[K] C) (h : C →ₗ[K] D)
    (hf : Function.Injective f) (hh : Function.Surjective h)
    (hfg : Function.Exact f g) (hgh : Function.Exact g h)
    (a : A →ₗ[K] A) (b : B →ₗ[K] B) (c : C →ₗ[K] C) (d : D →ₗ[K] D)
    (hab : b ∘ₗ f = f ∘ₗ a) (hbc : c ∘ₗ g = g ∘ₗ b)
    (hcd : d ∘ₗ h = h ∘ₗ c) :
    trace K B b - trace K C c = trace K A a - trace K D d := by
  have hgf : g.comp f = 0 := by
    ext x
    exact (hfg (f x)).mpr ⟨x, rfl⟩
  let g' : B →ₗ[K] ker h := g.codRestrict (ker h) fun x =>
    (hgh (g x)).mpr ⟨x, rfl⟩
  let c' : ker h →ₗ[K] ker h := (c.domRestrict (ker h)).codRestrict (ker h) fun x => by
    change h (c x) = 0
    have he := LinearMap.congr_fun hcd (x : C)
    change d (h x) = h (c x) at he
    exact he.symm.trans (by rw [x.property, map_zero])
  let S : ShortComplex (ModuleCat.{v} K) :=
    ShortComplex.moduleCatMk f g' (by ext x; exact DFunLike.congr_fun hgf x)
  have hS : S.ShortExact := {
    exact := (S.moduleCat_exact_iff).mpr fun x hx =>
      (hfg x).mp (congrArg Subtype.val hx)
    mono_f := (ModuleCat.mono_iff_injective _).mpr hf
    epi_g := (ModuleCat.epi_iff_surjective _).mpr (show Function.Surjective g' from fun x => by
      obtain ⟨z, hz⟩ := (hgh (x : C)).mp x.property
      exact ⟨z, Subtype.ext hz⟩) }
  let T := h.shortComplexKer
  let α : S ⟶ S := {
    τ₁ := ModuleCat.ofHom a
    τ₂ := ModuleCat.ofHom b
    τ₃ := ModuleCat.ofHom c'
    comm₁₂ := ModuleCat.hom_ext hab.symm
    comm₂₃ := by
      apply ModuleCat.hom_ext
      ext x
      change g' (b x) = c' (g' x)
      apply Subtype.ext
      exact (LinearMap.congr_fun hbc x).symm }
  let β : T ⟶ T := {
    τ₁ := ModuleCat.ofHom c'
    τ₂ := ModuleCat.ofHom c
    τ₃ := ModuleCat.ofHom d
    comm₁₂ := by ext x; rfl
    comm₂₃ := ModuleCat.hom_ext hcd.symm }
  let : Module.Free K S.X₁ := inferInstanceAs (Module.Free K A)
  let : Module.Finite K S.X₁ := inferInstanceAs (Module.Finite K A)
  let : Module.Free K S.X₂ := inferInstanceAs (Module.Free K B)
  let : Module.Finite K S.X₂ := inferInstanceAs (Module.Finite K B)
  let : Module.Free K S.X₃ := inferInstanceAs (Module.Free K (ker h))
  let : Module.Finite K S.X₃ := inferInstanceAs (Module.Finite K (ker h))
  let : Module.Free K T.X₁ := inferInstanceAs (Module.Free K (ker h))
  let : Module.Finite K T.X₁ := inferInstanceAs (Module.Finite K (ker h))
  let : Module.Free K T.X₂ := inferInstanceAs (Module.Free K C)
  let : Module.Finite K T.X₂ := inferInstanceAs (Module.Finite K C)
  let : Module.Free K T.X₃ := inferInstanceAs (Module.Free K D)
  let : Module.Finite K T.X₃ := inferInstanceAs (Module.Finite K D)
  have hleft := ShortComplex.trace_of_shortExact hS α
  have hright := ShortComplex.trace_of_shortExact (h.shortExact_shortComplexKer hh) β
  change trace K B b = trace K A a + trace K (ker h) c' at hleft
  change trace K C c = trace K (ker h) c' + trace K D d at hright
  linear_combination hleft - hright

end LinearMap

namespace ModuleCat

variable {K : Type u} [CommRing K] {A B : ModuleCat.{v} K}

theorem trace_eq_of_iso [Module.Free K A] [Module.Finite K A]
    [Module.Free K B] [Module.Finite K B]
    (e : A ≅ B) (f : A ⟶ A) (g : B ⟶ B) (h : f ≫ e.hom = e.hom ≫ g) :
    LinearMap.trace K A f.hom = LinearMap.trace K B g.hom := by
  have hg : (e.inv ≫ f) ≫ e.hom = g := by
    rw [Category.assoc, h, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  rw [← hg]
  change LinearMap.trace K A f.hom =
    LinearMap.trace K B (e.hom.hom ∘ₗ (e.inv ≫ f).hom)
  rw [LinearMap.trace_comp_comm']
  change LinearMap.trace K A f.hom = LinearMap.trace K A (e.hom ≫ e.inv ≫ f).hom
  rw [← Category.assoc, e.hom_inv_id, Category.id_comp]

end ModuleCat
