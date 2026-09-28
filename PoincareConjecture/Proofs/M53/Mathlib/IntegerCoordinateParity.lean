import PoincareConjecture.Proofs.M53.Mathlib.EvenEquiv
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Algebra.Group.Hom.Basic











set_option autoImplicit false

namespace AddMonoidHom




theorem even_apply_of_integer_coordinates
    {D A T : Type*} [AddCommGroup D] [AddCommGroup A] [AddCommGroup T]
    (f : D →+ A) (p q : A →+ ℤ) (δ : A →+ T)
    (hpair : Function.Bijective (fun a => (p a, q a)))
    (hp : Function.Bijective (p.comp f)) (hq : Function.Bijective (q.comp f))
    (hδ : δ.comp f = 0) (a : A) (ha : Even (p a) ↔ Even (q a)) :
    Even (δ a) := by
  obtain ⟨d, hd⟩ := hp.2 (p a)
  change p (f d) = p a at hd
  have hfd : Even (p (f d)) ↔ Even (q (f d)) :=
    ((AddEquiv.ofBijective (p.comp f) hp).even_apply_iff d).trans
      ((AddEquiv.ofBijective (q.comp f) hq).even_apply_iff d).symm
  rw [hd] at hfd
  obtain ⟨m, hm⟩ := Int.even_sub.mpr (ha.symm.trans hfd)
  obtain ⟨b, hb⟩ := hpair.2 (0, m)
  have hpb : p b = 0 := congrArg Prod.fst hb
  have hqb : q b = m := congrArg Prod.snd hb
  have hab : a - f d = b + b := by
    apply hpair.1
    apply Prod.ext
    · simp only [map_sub, map_add, hd, hpb, sub_self, add_zero]
    · simpa only [map_sub, map_add, hqb] using hm
  have hδfd : δ (f d) = 0 := by
    change (δ.comp f) d = 0
    rw [hδ]
    rfl
  refine ⟨δ b, ?_⟩
  have h := congrArg δ hab
  simpa only [map_sub, map_add, hδfd, sub_zero] using h

end AddMonoidHom
