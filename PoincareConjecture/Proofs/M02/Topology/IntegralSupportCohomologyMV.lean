import PoincareConjecture.Proofs.M02.Topology.IntegralSupportCohomologyComparison
import PoincareConjecture.Proofs.M02.Topology.IntegralDualBiprod

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits HomologicalComplex Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X]

abbrev integralSupportCochains (K : Set X) := integralRelativeCochains Kᶜ

def integralSupportCochainPushforward {K L : Set X} (h : K ⊆ L) :
    integralSupportCochains K ⟶ integralSupportCochains L :=
  integralDualMap (integralSupportRestriction h)

def integralSupportCochainDifference (K L : Set X) :
    integralSupportCochains (K ∩ L) ⟶ integralSupportCochains K ⊞ integralSupportCochains L :=
  biprod.lift (integralSupportCochainPushforward inter_subset_left)
    (-integralSupportCochainPushforward inter_subset_right)

def integralSupportCochainSum (K L : Set X) :
    integralSupportCochains K ⊞ integralSupportCochains L ⟶ integralSupportCochains (K ∪ L) :=
  biprod.desc (integralSupportCochainPushforward subset_union_left)
    (integralSupportCochainPushforward subset_union_right)

@[reassoc (attr := simp)]
theorem integralSupportCochainDifference_sum (K L : Set X) :
    integralSupportCochainDifference K L ≫ integralSupportCochainSum K L = 0 := by
  rw [integralSupportCochainDifference, integralSupportCochainSum, biprod.lift_desc,
    Preadditive.neg_comp]
  dsimp only [integralSupportCochainPushforward]
  rw [← integralDualMap_comp, ← integralDualMap_comp,
    integralSupportRestriction_comp, integralSupportRestriction_comp, add_neg_cancel]

def integralSupportDualSequence (K L : Set X) :
    ShortComplex (CochainComplex (ModuleCat.{u} Int) Nat) :=
  ShortComplex.mk
    (integralDualMap (integralSumDifference Kᶜ Lᶜ) ≫
      (integralDualBiprodIso (integralSupportChains K) (integralSupportChains L)).hom)
    ((integralDualBiprodIso (integralSupportChains K) (integralSupportChains L)).inv ≫
      integralDualMap (integralSupportUnionMap K L)) (by
        rw [Category.assoc, Iso.hom_inv_id_assoc, ← integralDualMap_comp]
        exact congrArg integralDualMap (integralSupportIntermediateSequence K L).zero |>.trans
          integralDualMap_zero)

def integralSupportDualSequenceIso (K L : Set X) :
    integralDualSequence (integralSupportIntermediateSequence K L) ≅
      integralSupportDualSequence K L :=
  ShortComplex.isoMk (Iso.refl _)
    (integralDualBiprodIso (integralSupportChains K) (integralSupportChains L))
    (Iso.refl _) (by
      simp [integralSupportDualSequence, integralDualSequence, integralSupportIntermediateSequence])
      (by
        simp [integralSupportDualSequence, integralDualSequence,
          integralSupportIntermediateSequence])

theorem integralSupportDualSequence_shortExact' (K L : Set X) :
    (integralSupportDualSequence K L).ShortExact :=
  ShortComplex.shortExact_of_iso (integralSupportDualSequenceIso K L)
    (integralSupportDualSequence_shortExact K L)

theorem integralSupportDualSequence_g (K L : Set X) :
    (integralSupportDualSequence K L).g = integralSupportCochainSum K L := by
  apply biprod.hom_ext'
  · dsimp only [integralSupportDualSequence, integralDualBiprodIso,
      integralSupportCochainSum, integralSupportCochainPushforward]
    rw [← Category.assoc, biprod.inl_desc, ← integralDualMap_comp,
      integralSupportUnionMap, biprod.lift_fst, biprod.inl_desc]
  · dsimp only [integralSupportDualSequence, integralDualBiprodIso,
      integralSupportCochainSum, integralSupportCochainPushforward]
    rw [← Category.assoc, biprod.inr_desc, ← integralDualMap_comp,
      integralSupportUnionMap, biprod.lift_snd, biprod.inr_desc]

@[reassoc (attr := simp)]
theorem integralSupportDualComparison_f (K L : Set X) :
    integralDualMap (integralSupportComparison K L) ≫ (integralSupportDualSequence K L).f =
      integralSupportCochainDifference K L := by
  apply biprod.hom_ext
  · dsimp only [integralSupportDualSequence]
    rw [Category.assoc, Category.assoc, integralDualBiprodIso_hom_fst,
      ← integralDualMap_comp, ← integralDualMap_comp]
    rw [integralSumDifference, biprod.inl_desc, integralSupportComparison_left]
    simp only [integralSupportCochainDifference, biprod.lift_fst]
    rfl
  · dsimp only [integralSupportDualSequence]
    rw [Category.assoc, Category.assoc, integralDualBiprodIso_hom_snd,
      ← integralDualMap_comp, ← integralDualMap_comp]
    rw [integralSumDifference, biprod.inr_desc, Preadditive.neg_comp,
      integralSupportComparison_right, integralDualMap_neg]
    simp only [integralSupportCochainDifference, biprod.lift_snd]
    rfl

theorem integralSupportComparison_dual_quasiIso
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) :
    QuasiIso (integralDualMap (integralSupportComparison K L)) := by
  let : ∀ n, CategoryTheory.Projective ((integralSumQuotient Kᶜ Lᶜ).X n) :=
    integralSumQuotient_projective Kᶜ Lᶜ
  let : ∀ n, CategoryTheory.Projective ((integralSupportChains (K ∩ L)).X n) :=
    integralRelativeChains_projective (K ∩ L)ᶜ
  apply integralDualMap_quasiIso_of_projective
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact integralSupportComparison_homology_isIso K L hK hL n

def integralSupportCohomologyIntersectionIso
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (q : Nat) :
    integralSupportCohomology (K ∩ L) q ≅
      (integralDualComplex (integralSumQuotient Kᶜ Lᶜ)).homology q := by
  let := integralSupportComparison_dual_quasiIso K L hK hL
  exact asIso (homologyMap (integralDualMap (integralSupportComparison K L)) q)

def integralSupportCohomologyConnecting
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (q : Nat) :
    integralSupportCohomology (K ∪ L) q ⟶ integralSupportCohomology (K ∩ L) (q + 1) :=
  (integralSupportDualSequence_shortExact' K L).δ q (q + 1) rfl ≫
    (integralSupportCohomologyIntersectionIso K L hK hL (q + 1)).inv

@[reassoc (attr := simp)]
theorem integralSupportCohomologyIntersectionIso_f
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (q : Nat) :
    (integralSupportCohomologyIntersectionIso K L hK hL q).hom ≫
        homologyMap (integralSupportDualSequence K L).f q =
      homologyMap (integralSupportCochainDifference K L) q := by
  change homologyMap (integralDualMap (integralSupportComparison K L)) q ≫ _ = _
  exact (homologyMap_comp (integralDualMap (integralSupportComparison K L))
    (integralSupportDualSequence K L).f q).symm.trans
      (congrArg (fun f => homologyMap f q) (integralSupportDualComparison_f K L))

@[reassoc (attr := simp)]
theorem integralSupportCohomologyIntersectionIso_inv_f
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (q : Nat) :
    (integralSupportCohomologyIntersectionIso K L hK hL q).inv ≫
        homologyMap (integralSupportCochainDifference K L) q =
      homologyMap (integralSupportDualSequence K L).f q := by
  rw [← integralSupportCohomologyIntersectionIso_f K L hK hL q, Iso.inv_hom_id_assoc]

def integralSupportCohomologyMayerVietoris (K L : Set X) (q : Nat) :
    ShortComplex (ModuleCat.{u} Int) :=
  ShortComplex.mk (homologyMap (integralSupportCochainDifference K L) q)
    (homologyMap (integralSupportCochainSum K L) q) (by
      rw [← homologyMap_comp, integralSupportCochainDifference_sum, homologyMap_zero])

theorem integralSupportCohomologyMayerVietoris_exact
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (q : Nat) :
    (integralSupportCohomologyMayerVietoris K L q).Exact := by
  let S := integralSupportDualSequence K L
  let hS := integralSupportDualSequence_shortExact' K L
  let e : (ShortComplex.mk (homologyMap S.f q) (homologyMap S.g q)
      (by rw [← homologyMap_comp, S.zero, homologyMap_zero])) ≅
      integralSupportCohomologyMayerVietoris K L q :=
    ShortComplex.isoMk (integralSupportCohomologyIntersectionIso K L hK hL q).symm
      (Iso.refl _) (Iso.refl _) (by
        change (integralSupportCohomologyIntersectionIso K L hK hL q).inv ≫
          homologyMap (integralSupportCochainDifference K L) q = homologyMap S.f q ≫ 𝟙 _
        rw [Category.comp_id]
        exact integralSupportCohomologyIntersectionIso_inv_f K L hK hL q)
      (by
        change 𝟙 _ ≫ homologyMap (integralSupportCochainSum K L) q = homologyMap S.g q ≫ 𝟙 _
        rw [Category.id_comp, Category.comp_id]
        exact congrArg (fun f => homologyMap f q) (integralSupportDualSequence_g K L).symm)
  exact ShortComplex.exact_of_iso e (hS.homology_exact₂ q)

@[reassoc (attr := simp)]
theorem integralSupportCohomologySum_connecting
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (q : Nat) :
    homologyMap (integralSupportCochainSum K L) q ≫
      integralSupportCohomologyConnecting K L hK hL q = 0 := by
  let hS := integralSupportDualSequence_shortExact' K L
  change homologyMap (integralSupportCochainSum K L) q ≫
    (hS.δ q (q + 1) (show (ComplexShape.up Nat).Rel q (q + 1) from rfl) ≫
      (integralSupportCohomologyIntersectionIso K L hK hL (q + 1)).inv) = 0
  rw [← Category.assoc, ← integralSupportDualSequence_g, hS.comp_δ, zero_comp]

@[reassoc (attr := simp)]
theorem integralSupportCohomologyConnecting_difference
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (q : Nat) :
    integralSupportCohomologyConnecting K L hK hL q ≫
      homologyMap (integralSupportCochainDifference K L) (q + 1) = 0 := by
  let hS := integralSupportDualSequence_shortExact' K L
  change (hS.δ q (q + 1) (show (ComplexShape.up Nat).Rel q (q + 1) from rfl) ≫
    (integralSupportCohomologyIntersectionIso K L hK hL (q + 1)).inv) ≫
      homologyMap (integralSupportCochainDifference K L) (q + 1) = 0
  rw [Category.assoc, integralSupportCohomologyIntersectionIso_inv_f, hS.δ_comp]

theorem integralSupportCohomologyMayerVietoris_exact_union
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (q : Nat) :
    (ShortComplex.mk (homologyMap (integralSupportCochainSum K L) q)
      (integralSupportCohomologyConnecting K L hK hL q)
      (integralSupportCohomologySum_connecting K L hK hL q)).Exact := by
  let hS := integralSupportDualSequence_shortExact' K L
  let e := ShortComplex.isoMk (Iso.refl _ ) (Iso.refl _)
    (integralSupportCohomologyIntersectionIso K L hK hL (q + 1)).symm
    (S₁ := ShortComplex.mk _ _ (hS.comp_δ q (q + 1) rfl))
    (S₂ := ShortComplex.mk _ _ (integralSupportCohomologySum_connecting K L hK hL q))
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
        exact congrArg (fun f => homologyMap f q) (integralSupportDualSequence_g K L).symm)
    (by simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom]
        rfl)
  exact ShortComplex.exact_of_iso e (hS.homology_exact₃ q (q + 1) rfl)

theorem integralSupportCohomologyMayerVietoris_exact_intersection
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (q : Nat) :
    (ShortComplex.mk (integralSupportCohomologyConnecting K L hK hL q)
      (homologyMap (integralSupportCochainDifference K L) (q + 1))
      (integralSupportCohomologyConnecting_difference K L hK hL q)).Exact := by
  let hS := integralSupportDualSequence_shortExact' K L
  let e := ShortComplex.isoMk (Iso.refl _)
    (integralSupportCohomologyIntersectionIso K L hK hL (q + 1)).symm (Iso.refl _)
    (S₁ := ShortComplex.mk _ _ (hS.δ_comp q (q + 1) rfl))
    (S₂ := ShortComplex.mk _ _ (integralSupportCohomologyConnecting_difference K L hK hL q))
    (by simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom]
        rfl)
    (by simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
        exact integralSupportCohomologyIntersectionIso_inv_f K L hK hL (q + 1))
  exact ShortComplex.exact_of_iso e (hS.homology_exact₁ q (q + 1) rfl)

theorem integralSupportCohomologyConnecting_one_eq
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) {T : ModuleCat.{u} Int}
    (z : T ⟶ (integralSupportCochains (K ∪ L)).X 1)
    (hz : z ≫ (integralSupportCochains (K ∪ L)).d 1 2 = 0)
    (b : T ⟶ (integralSupportCochains K ⊞ integralSupportCochains L).X 1)
    (hb : b ≫ (integralSupportCochainSum K L).f 1 = z)
    (gamma : T ⟶ (integralSupportCochains (K ∩ L)).X 2)
    (hgamma : gamma ≫ (integralSupportCochains (K ∩ L)).d 2 3 = 0)
    (hboundary : gamma ≫ (integralSupportCochainDifference K L).f 2 =
      b ≫ (integralSupportCochains K ⊞ integralSupportCochains L).d 1 2) :
    (integralSupportCochains (K ∪ L)).liftCycles z 2
        ((ComplexShape.up Nat).next_eq' (show (ComplexShape.up Nat).Rel 1 2 from rfl)) hz ≫
        (integralSupportCochains (K ∪ L)).homologyπ 1 ≫
        integralSupportCohomologyConnecting K L hK hL 1 =
      (integralSupportCochains (K ∩ L)).liftCycles gamma 3
        ((ComplexShape.up Nat).next_eq' (show (ComplexShape.up Nat).Rel 2 3 from rfl)) hgamma ≫
        (integralSupportCochains (K ∩ L)).homologyπ 2 := by
  let S := integralSupportDualSequence K L
  let hS := integralSupportDualSequence_shortExact' K L
  let F := integralDualMap (integralSupportComparison K L)
  have hnext1 : (ComplexShape.up Nat).next 1 = 2 := by
    exact (ComplexShape.up Nat).next_eq' (show (ComplexShape.up Nat).Rel 1 2 from rfl)
  have hnext2 : (ComplexShape.up Nat).next 2 = 3 := by
    exact (ComplexShape.up Nat).next_eq' (show (ComplexShape.up Nat).Rel 2 3 from rfl)
  have hb' : b ≫ S.g.f 1 = z := by
    rw [integralSupportDualSequence_g]
    exact hb
  have hg' : (gamma ≫ F.f 2) ≫ S.f.f 2 = b ≫ S.X₂.d 1 2 := by
    rw [Category.assoc]
    have hf := congrArg (fun f => f.f 2) (integralSupportDualComparison_f K L)
    change F.f 2 ≫ S.f.f 2 = (integralSupportCochainDifference K L).f 2 at hf
    rw [hf]
    exact hboundary
  have he := hS.δ_eq 1 2 rfl z hz b hb' (gamma ≫ F.f 2) hg' 3 hnext2
  have hn : (integralSupportCochains (K ∩ L)).liftCycles gamma 3 hnext2 hgamma ≫
      (integralSupportCochains (K ∩ L)).homologyπ 2 ≫ homologyMap F 2 =
      S.X₁.liftCycles (gamma ≫ F.f 2) 3 hnext2 (by
        change (gamma ≫ F.f 2) ≫ (integralDualComplex (integralSumQuotient Kᶜ Lᶜ)).d 2 3 = 0
        rw [Category.assoc, F.comm, ← Category.assoc, hgamma, zero_comp]) ≫
          S.X₁.homologyπ 2 := by
    rw [homologyπ_naturality]
    exact liftCycles_comp_cyclesMap_assoc gamma 3 hnext2 hgamma F _
  have he' := he.trans hn.symm
  let e := integralSupportCohomologyIntersectionIso K L hK hL 2
  change S.X₃.liftCycles z 2 hnext1 hz ≫ S.X₃.homologyπ 1 ≫ hS.δ 1 2 rfl =
    (integralSupportCochains (K ∩ L)).liftCycles gamma 3 hnext2 hgamma ≫
      (integralSupportCochains (K ∩ L)).homologyπ 2 ≫ e.hom at he'
  have hfinal := congrArg (fun f => f ≫ e.inv) he'
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hfinal
  change S.X₃.liftCycles z 2 hnext1 hz ≫ S.X₃.homologyπ 1 ≫
    hS.δ 1 2 rfl ≫ e.inv =
      (integralSupportCochains (K ∩ L)).liftCycles gamma 3 hnext2 hgamma ≫
        (integralSupportCochains (K ∩ L)).homologyπ 2
  exact hfinal

end PoincareConjecture.Proofs.M02.Topology
