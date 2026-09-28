import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.SameCollarAnnulusCancellation









set_option autoImplicit false
open Set Metric Geometry TriangularRoofModel PLAnnularStrip

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "Annulus" => squareAnnulus 8 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-(1/2 : ℝ)) (1/2)

theorem exists_original_collar_exchanges
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R H K : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (B : Bool → Set X)
    (sB : ∀ b, ChartwisePLSphere e (B b))
    (hH : IsCompact H) (he : PLDomain e H) (hKH : K ⊆ H)
    (hdis : Disjoint (B false) (B true))
    (hR : R = H ∩ (interior K)ᶜ) (hK : frontier K = B false ∪ B true)
    (hsmall : MapsTo P.map (Disk ×ˢ Icc (-1 : ℝ) 1) (interior H))
    (hstripK : P.closedStrip ∩ K = P.map '' (Rim ×ˢ J))
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (N.space ×ˢ Icc (-1 : ℝ) 1))
    (hci : InjOn c (N.space ×ˢ Icc (-1 : ℝ) 1))
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1)
    (hKeq : K = c '' (N.space ×ˢ Icc (-ε) ε))
    (hBeq : ∀ a, B a = c '' (N.space ×ˢ {if a then ε else -ε})) :
    ∃ (owner : Bool) (F : V3 × ℝ → X) (g : P2 → V3)
      (k q : Bool → Set V3) (C : Bool → Set (V3 × ℝ)),
      PolyhedralPLInCharts e F (Sphere ×ˢ I) ∧ InjOn F (Sphere ×ˢ I) ∧
      F '' (Sphere ×ˢ I) = K ∧
      (∀ x ∈ Sphere, F (x,1) = (sB owner).map x) ∧
      F '' (Sphere ×ˢ {(0 : ℝ)}) = B (!owner) ∧
      (∀ d, P.map '' (Rim ×ˢ J) ⊆ B d ↔ d = owner) ∧
      FinitePiecewiseAffineOn g Annulus ∧ MapsTo g Annulus Sphere ∧
      (sB owner).map '' (g '' Annulus) = P.map '' (Rim ×ˢ J) ∧
      (∀ a, IsFinitePLBallPair P2 (k a) (q a) ∧ k a ⊆ Sphere ∧
        IsFinitePLBallPair P2 (Sphere \ (k a \ q a)) (q a) ∧
        (sB owner).map '' q a = P.map '' (Rim ×ˢ {if a then (1/2 : ℝ) else -(1/2)}) ∧
        ((sB owner).map '' k a) ∩ (P.map '' (Rim ×ˢ J)) = (sB owner).map '' q a) ∧
      Disjoint ((sB owner).map '' k true) ((sB owner).map '' k false) ∧
      (((sB owner).map '' k true) ∪ ((sB owner).map '' k false)) ∪
        (P.map '' (Rim ×ˢ J)) = B owner ∧
      ∀ a,
        let A := Sphere \ (k a \ q a)
        ∃ (W : ((F '' (A ×ˢ I)) ∪ P.closedStrip : Set X) ≃ₜ
            (frontier (halfBall 1) ×ˢ I : Set (P3 × ℝ)))
          (σ : P3 × ℝ → X),
          PolyhedralPLInCharts e σ (frontier (halfBall 1) ×ˢ I) ∧
          (∀ z : (frontier (halfBall 1) ×ˢ I : Set (P3 × ℝ)), σ z = (W.symm z : X)) ∧
          (∀ x : ((F '' (A ×ˢ I)) ∪ P.closedStrip : Set X),
            (x : X) ∈ (F '' C a) ∪
              (P.map '' (Disk ×ˢ {if a then (1/2 : ℝ) else -(1/2)})) ↔
              (W x : P3 × ℝ).2 = if a then (1 : ℝ) else 0) ∧
          (∀ x : ((F '' (A ×ˢ I)) ∪ P.closedStrip : Set X),
            (x : X) ∈ ((sB owner).map '' k (!a)) ∪
              (P.map '' (Disk ×ˢ {if !a then (1/2 : ℝ) else -(1/2)})) ↔
              (W x : P3 × ℝ).2 = if !a then (1 : ℝ) else 0) ∧
          frontier ((F '' (A ×ˢ I)) ∪ P.closedStrip) =
            ((F '' C a) ∪
              (P.map '' (Disk ×ˢ {if a then (1/2 : ℝ) else -(1/2)}))) ∪
            (((sB owner).map '' k (!a)) ∪
              (P.map '' (Disk ×ˢ {if !a then (1/2 : ℝ) else -(1/2)}))) := by
  obtain ⟨owner,g,k,q,C,howner,hg,hgS,hgimage,hk,hkd,hcover,hprod⟩ :=
    P.exists_exterior_annulus_disks B sB he.compatible hdis hR hK hsmall
  obtain ⟨F,hF,hFi,hFK,hFtop,_,hFbottom⟩ := (sB owner).exists_same_collar_coordinates
    he.compatible N hN c hc hci hε hεle owner (hBeq owner)
  have hFK' : F '' (Sphere ×ˢ I) = K := hFK.trans hKeq.symm
  have hFbottom' : F '' (Sphere ×ˢ {(0 : ℝ)}) = B (!owner) := by
    rw [hFbottom,hBeq]
    cases owner <;> rfl
  have htop (A : Set V3) (hAS : A ⊆ Sphere) :
      F '' (A ×ˢ {(1 : ℝ)}) = (sB owner).map '' A := by
    ext x
    constructor
    · rintro ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
      have ht1 : t = 1 := ht
      subst t
      exact ⟨z,hz,(hFtop z (hAS hz)).symm⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨(z,1),⟨hz,rfl⟩,hFtop z (hAS hz)⟩
  have hband : F '' ((g '' Annulus) ×ˢ {(1 : ℝ)}) = P.map '' (Rim ×ˢ J) :=
    (htop (g '' Annulus) (by rintro _ ⟨z,hz,rfl⟩; exact hgS hz)).trans hgimage
  have hrim (s : Bool) : F '' (q s ×ˢ {(1 : ℝ)}) =
      P.map '' (Rim ×ˢ {if s then (1/2 : ℝ) else -(1/2)}) :=
    (htop (q s) ((hk s).1.1.trans (hk s).2.1)).trans (hk s).2.2.2.1
  refine ⟨owner,F,g,k,q,C,hF,hFi,hFK',hFtop,hFbottom',howner,hg,hgS,hgimage,
    (fun a => ⟨(hk a).1,(hk a).2.1,(hprod a).1,(hk a).2.2.2.1,(hk a).2.2.2.2⟩),
    hkd,hcover,?_⟩
  intro a
  obtain ⟨hA,hAeq,hC,hcap,hball,hmeet,hcapmeet,hcapdis⟩ := hprod a
  let A := Sphere \ (k a \ q a)
  let D : Bool → Set (V3 × ℝ) := fun s => if s = a then C a else k (!a) ×ˢ {(1 : ℝ)}
  have hD (s : Bool) : IsFinitePLBallPair P2 (D s) (q s ×ˢ {(1 : ℝ)}) := by
    cases a <;> cases s <;> simp only [D,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,Bool.true_eq_false,↓reduceIte]
    · exact hC
    · exact hcap
    · exact hcap
    · exact hC
  have hDmeet (s : Bool) : D s ∩ ((g '' Annulus) ×ˢ {(1 : ℝ)}) = q s ×ˢ {(1 : ℝ)} := by
    cases a <;> cases s <;> simp only [D,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,Bool.true_eq_false,↓reduceIte]
    · exact hmeet
    · exact hcapmeet
    · exact hcapmeet
    · exact hmeet
  have hDdis : Disjoint (D true) (D false) := by
    cases a
    · simpa [D] using hcapdis
    · simpa [D] using hcapdis.symm
  have hDball : IsFinitePLBallPair P3 (A ×ˢ I)
      (((g '' Annulus) ×ˢ {(1 : ℝ)}) ∪ (D false ∪ D true)) := by
    cases a
    · simpa [D,A] using hball
    · simpa only [D,Bool.false_eq_true,↓reduceIte,Bool.not_true,union_comm (C true)] using hball
  obtain ⟨W,σ,hσ,hσval,hmark,hfront⟩ := P.exists_same_collar_strip_product_of_marked_caps
    hH he (fun z hz => interior_subset (hsmall hz)) hKH F hF hFi hFK'
    (show A ⊆ Sphere from sdiff_subset) (subset_union_right.trans hAeq.subset)
    hband hstripK D q hDball hD hDmeet hDdis hrim
  refine ⟨W,σ,hσ,hσval,?_,?_,?_⟩
  · intro x
    simpa only [D,↓reduceIte] using hmark a x
  · intro x
    have hne : (!a) ≠ a := by cases a <;> decide
    simpa only [D,if_neg hne,htop (k (!a)) (hk (!a)).2.1] using hmark (!a) x
  · cases a
    · simpa [D,htop (k true) (hk true).2.1] using hfront
    · simpa [D,htop (k false) (hk false).2.1,union_comm] using hfront

end PoincareConjecture.M76.OriginalDiskProduct
