import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Cutting.OriginalFiveCaseNoL3
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Complement.OriginalCollarExchange

/-!
# Constructing an original collar exchange with no PL punctured components

The finite original sphere collar constructs the retained disks and both
exchange products. The five-case argument selects one and supplies a
chartwise PL middle sphere with a compact PL product neighborhood. Its
literal exterior has no marked PL punctured-sphere component, and the
new neighborhood stays inside the original sphere-and-disk support.
-/

set_option autoImplicit false
open Set Metric Geometry TriangularRoofModel

namespace PoincareMT.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem exists_original_exchange_without_punctured_components
    {X E A ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    {e : ι → OpenPartialHomeomorph X V3} {R K : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e (R ∩ (interior K)ᶜ) j)
    (hR : IsCompact R) (hRc : IsConnected R) (he : PLDomain e R)
    (hK : PLDomain e K) (hKc : IsConnected K) (hKR : K ⊆ interior R)
    (B : Bool → Set X) (sB : ∀ b, ChartwisePLSphere e (B b))
    (hBdis : Disjoint (B false) (B true)) (hfrontK : frontier K = B false ∪ B true)
    (hsmall : MapsTo P.map (Disk ×ˢ Icc (-1 : ℝ) 1) (interior R))
    (hstripK : P.closedStrip ∩ K = P.map '' (Rim ×ˢ J))
    (hDPL : PLDomain e (K ∪ P.closedStrip))
    (hDfront : frontier (K ∪ P.closedStrip) = (frontier K \ P.openStrip) ∪ P.endDisks)
    (hopen : IsOpen ((Subtype.val : (R ∩ (interior K)ᶜ : Set X) → X) ⁻¹' P.openStrip))
    (N : SimplicialComplex ℝ A) (hN : N.faces.Finite) (c : A × ℝ → X)
    (hc : PolyhedralPLInCharts e c (N.space ×ˢ Icc (-1 : ℝ) 1))
    (hci : InjOn c (N.space ×ˢ Icc (-1 : ℝ) 1))
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1)
    (hKeq : K = c '' (N.space ×ˢ Icc (-ε) ε))
    (hBeq : ∀ a, B a = c '' (N.space ×ˢ {if a then ε else -ε}))
    (f : X → E) (L : SimplicialComplex ℝ E) (g : E → X)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ R, f x ∈ L.space ∧ g (f x) = x)
    (hno : ∀ x ∈ R ∩ (interior K)ᶜ,
      ¬ HasPuncturedSphereModel e f (connectedComponentIn (R ∩ (interior K)ᶜ) x)) :
    ∃ (U : Set X) (W : U ≃ₜ (frontier (halfBall 1) ×ˢ I : Set (P3 × ℝ)))
      (σ : P3 × ℝ → X),
      PolyhedralPLInCharts e σ (frontier (halfBall 1) ×ˢ I) ∧
      (∀ z : (frontier (halfBall 1) ×ˢ I : Set (P3 × ℝ)), σ z = (W.symm z : X)) ∧
      Nonempty (ChartwisePLSphere e (σ '' (frontier (halfBall 1) ×ˢ {(1 / 2 : ℝ)}))) ∧
      σ '' (frontier (halfBall 1) ×ˢ {(1 / 2 : ℝ)}) ⊆ interior U ∧
      IsCompact U ∧ PLDomain e U ∧ U ⊆ K ∪ P.closedStrip ∧
      ∀ x ∈ R ∩ (interior U)ᶜ,
        ¬ HasPuncturedSphereModel e f (connectedComponentIn (R ∩ (interior U)ᶜ) x) := by
  obtain ⟨owner, F, annulusMap, k, q, C, hF, hFi, hFK, htop, hbottom, howner,
      _, _, _, hk, hkdis, hcover, hproducts⟩ :=
    P.exists_original_collar_exchanges B sB hR he (hKR.trans interior_subset)
      hBdis rfl hfrontK hsmall hstripK N hN c hc hci hε hεle hKeq hBeq
  have hk' (b : Bool) : IsFinitePLBallPair (ℝ × ℝ) (k b) (q b) ∧ k b ⊆ Sphere ∧
      (sB owner).map '' q b = P.capRimSet b ∧
      ((sB owner).map '' k b) ∩ (P.map '' (Rim ×ˢ J)) = (sB owner).map '' q b :=
    ⟨(hk b).1, (hk b).2.1, (hk b).2.2.2.1, (hk b).2.2.2.2⟩
  obtain ⟨b, hnew⟩ := P.exists_same_collar_exchange_without_punctured_components
    hR hRc he hK hKc hKR B sB hBdis hfrontK hsmall hstripK hDPL hDfront hopen
    owner k q howner hk' (fun b => (hk b).2.2.1) hkdis hcover
    F hF hFi hFK htop hbottom (fun b => by
      obtain ⟨W, σ, hσ, hσval, hmark, hmarkOther, hfront⟩ := hproducts b
      exact ⟨(F '' C b) ∪ P.capDisk b, W, σ, hσ, hσval, hmark, hmarkOther, hfront⟩)
    f L g hf hg hgi hreal hno
  obtain ⟨W, σ, hσ, hσval, _, _, _⟩ := hproducts b
  let U := (F '' ((Sphere \ (k b \ q b)) ×ˢ I)) ∪ P.closedStrip
  have hUc : IsCompact U :=
    (((hk b).2.2.1.isCompact.prod isCompact_Icc).image_of_continuousOn
      (hF.continuousOn.mono (prod_mono sdiff_subset subset_rfl))).union
      (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have hUsub : U ⊆ K ∪ P.closedStrip := union_subset_union
    ((image_mono (prod_mono sdiff_subset subset_rfl)).trans hFK.subset) subset_rfl
  have hQeq : P.cutCarrier = R ∩ (interior (K ∪ P.closedStrip))ᶜ :=
    (P.global_common_cut_geometry hR he hDPL hKR rfl hsmall hDfront).2.1.symm
  obtain ⟨_, _, hout⟩ := P.retained_collar_exchange_exterior
    (sB owner) F hF hFi hFK htop hstripK ((howner owner).mpr rfl)
    (hk b).1 (hk b).2.1 (hk b).2.2.2.2 b (hk b).2.2.2.1 R
    (hKR.trans interior_subset)
  rw [← hQeq] at hout
  have hmiddle : σ '' (frontier (halfBall 1) ×ˢ {(1 / 2 : ℝ)}) ⊆ interior U := by
    rintro _ ⟨z, hz, rfl⟩
    have hzt : z.2 = (1 / 2 : ℝ) := hz.2
    have hzI : z ∈ frontier (halfBall 1) ×ˢ I := ⟨hz.1, by rw [hzt]; norm_num⟩
    exact ((original_sphere_product_frontier W σ hσ hσval).2.1 ⟨z, hzI⟩).mpr
      (by change 0 < z.2 ∧ z.2 < 1; rw [hzt]; norm_num)
  refine ⟨U, W, σ, hσ, hσval,
    original_sphere_product_endpoint W σ hσ hσval (by norm_num), hmiddle, hUc,
    original_sphere_product_plDomain W σ hσ hσval he.compatible he.cover, hUsub, ?_⟩
  intro x hx
  change x ∈ R ∩ (interior ((F '' ((Sphere \ (k b \ q b)) ×ˢ I)) ∪ P.closedStrip))ᶜ at hx
  change ¬ HasPuncturedSphereModel e f (connectedComponentIn
    (R ∩ (interior ((F '' ((Sphere \ (k b \ q b)) ×ˢ I)) ∪ P.closedStrip))ᶜ) x)
  rw [hout] at hx ⊢
  exact hnew x hx

end PoincareMT.M76.OriginalDiskProduct
