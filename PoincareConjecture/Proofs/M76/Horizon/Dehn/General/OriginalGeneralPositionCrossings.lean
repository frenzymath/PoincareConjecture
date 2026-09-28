import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.OriginalGeneralPositionLinks
import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcCrossedStar
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInteriorChart

set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex Topology unitInterval
open scoped Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

set_option maxHeartbeats 1600000 in

theorem OriginalGeneralPositionData.exists_protected_crossed_charts_with_closed_support
    {s t : Stage e S f r C} {step : Step s t} {R Fmark : Set M}
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    {old : StageMarkedDisk t R Fmark base Jgroup}
    (data : OriginalGeneralPositionData step old)
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark)) :
  ∀ a b : D, a ≠ b → (a : V2) ∉ Rim →
    step.projection (step.inclusion (data.initial.map a)) =
      step.projection (step.inclusion (data.initial.map b)) →
    ∀ U : Set s.Carrier, IsOpen U →
      step.projection (step.inclusion (data.initial.map a)) ∈ U →
      ∃ (w : TwoBranchWindow (step.projection ∘ step.inclusion))
        (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3)
        (J P P₀ R₀ K K₀ L : SimplicialComplex ℝ V3)
        (q : V3 → ℝ × ℝ) (ρ δ : ℝ),
        data.initial.map a ∈ w.left.source ∧ data.initial.map b ∈ w.right.source ∧
        step.projection (step.inclusion (data.initial.map a)) ∈ Q.source ∧
        Q (step.projection (step.inclusion (data.initial.map a))) = 0 ∧
        Q.source ⊆ U ∩ interior (s.projection ⁻¹' R) ∧ Q.source ⊆ w.target ∧
        (∀ k, (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
        (∀ k, (t.charts k).symm.trans (w.left.trans Q) ∈ piecewiseAffineGroupoid V3 ∧
          (t.charts k).symm.trans (w.right.trans Q) ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ Q.source,
          y ∈ (step.projection ∘ step.inclusion) '' (data.initial.map '' D ∩ w.left.source) ↔
            (c (Q y)).2 = 0) ∧
        J.faces.Finite ∧ J.space ⊆ Q.target ∧ (0 : V3) ∈ interior J.space ∧
        0 < ρ ∧ ball (0 : V3) ρ ⊆ interior J.space ∧
        closedBall (0 : V3) ρ ⊆ interior J.space ∧
        P.space = (w.right.trans Q) ''
          (data.initial.map '' D ∩ (w.right.trans Q).source) ∩ J.space ∧
        P₀.space = P.space \ ball (0 : V3) ρ ∧
        R₀.faces.Finite ∧ R₀.IsSubdivision J ∧ K ≤ R₀ ∧ K.space = P.space ∧
        K.AffineOnFaces q ∧ InjOn q K.space ∧ K₀ ≤ K ∧ K₀.space = P₀.space ∧
        (∀ z ∈ P.space, z ∈ interior J.space → q z ∈ interior (q '' P.space)) ∧
        (step.projection ∘ step.inclusion) ⁻¹' (Q.symm '' J.space) =
          (w.left.trans Q).symm '' J.space ∪ (w.right.trans Q).symm '' J.space ∧
        (∀ v ∈ P₀.space, v ∈ interior J.space → (c v).2 = 0 →
          ∃ T : OpenPartialHomeomorph V3 C3,
            (0 : V3) ∈ T.source ∧ T 0 = 0 ∧
            LocallyPiecewiseAffineOn T.symm T.target ∧
            (∀ z ∈ T.source, z ∈ (fun x : V3 => -v + x) '' K.space ↔
              (T z).1.1 = 0) ∧
            ∀ z ∈ T.source, (c z).2 = 0 ↔ (T z).2 = 0) ∧
        (∀ v ∈ P₀.space, v ∈ interior J.space → (c v).2 = 0 →
          v ∈ closure (K.space ∩ {z | 0 < (c z).2}) ∧
          v ∈ closure (K.space ∩ {z | (c z).2 < 0})) ∧
        (∀ v ∈ K₀.vertices, v ∈ interior J.space → (c v).2 = 0 →
          ((K.link v).space ∩ {z | (c z).2 = 0}).ncard = 2 ∧
          (∃ z ∈ (K.link v).space, 0 < (c z).2) ∧
          ∃ z ∈ (K.link v).space, (c z).2 < 0) ∧
        (∀ v ∈ K.vertices, v ∈ interior J.space →
          ∃ (n : ℕ) (T : Polygon V3 (n + 3)), Function.Injective T ∧
            T.HasSimplicialEdges ∧ T.boundary ℝ = (K.link v).space) ∧
        L.faces.Finite ∧ L.space = J.space ∩ {z | (c z).2 = 0} ∧
        0 < δ ∧ (∀ v ∈ R₀.vertices, (c v).2 ≠ 0 → δ ≤ |(c v).2|) ∧
        ∀ ε : ℝ, 0 < ε → ∃ H : PLCarrierMotion J.space P₀.space ε,
          R₀.AffineOnFaces (H.map 1) ∧
          (∀ v ∈ R₀.vertices, (c v).2 ≠ 0 → ∀ u,
            (0 < (c (H.map u v)).2 ↔ 0 < (c v).2) ∧
            ((c (H.map u v)).2 < 0 ↔ (c v).2 < 0)) ∧
          (∀ v ∈ K.vertices,
            (c (H.map 1 v)).2 = 0 ↔ v ∈ K₀.vertices ∧ (c v).2 = 0) ∧
          (∀ face ∈ K.faces, (∀ v ∈ face, (c (H.map 1 v)).2 = 0) ↔
            face ∈ K₀.faces ∧ ∀ v ∈ face, (c v).2 = 0) ∧
          (∀ face ∈ K.faces, face ∉ K₀.faces → ∀ other ∈ L.faces,
            affineSpan ℝ (H.map 1 '' (face : Set V3) ∪ (other : Set V3)) = ⊤ ∨
              Disjoint (intrinsicInterior ℝ (convexHull ℝ (H.map 1 '' (face : Set V3))))
                (convexHull ℝ (other : Set V3))) ∧
          ∃ Kamb Knew : SimplicialComplex ℝ V3,
            Kamb.faces.Finite ∧ Kamb.space = J.space ∧ Knew ≤ Kamb ∧
            Knew.space = H.map 1 '' P.space ∧ K₀ ≤ Knew ∧
            Knew.AffineOnFaces (q ∘ (H.map 1).symm) ∧
            InjOn (q ∘ (H.map 1).symm) Knew.space ∧
            (∀ v ∈ K.vertices,
              (Knew.link (H.map 1 v)).space = H.map 1 '' (K.link v).space ∧
              (Knew.closedStar (H.map 1 v)).space = H.map 1 '' (K.closedStar v).space) ∧
            (∀ v ∈ K.vertices, v ∈ interior J.space →
              ∃ (n : ℕ) (T : Polygon V3 (n + 3)), Function.Injective T ∧
                T.HasSimplicialEdges ∧ T.boundary ℝ = (Knew.link (H.map 1 v)).space) ∧
          ∃ (G : I → t.Carrier ≃ₜ t.Carrier)
            (new : StageMarkedDisk t R Fmark base Jgroup),
          Continuous (fun z : I × t.Carrier => G z.1 z.2) ∧
          Continuous (fun z : I × t.Carrier => (G z.1).symm z.2) ∧
          (∀ x, G 0 x = x) ∧
          (∀ u, EqOn (G u)
            ((w.right.trans Q).symm ∘ H.map u ∘ (w.right.trans Q))
              (w.right.trans Q).source) ∧
          (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' J.space)ᶜ) ∧
          (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' P₀.space)) ∧
          (∀ u, EqOn (G u) id w.left.source) ∧
          (∀ u, EqOn (G u) id (frontier (t.projection ⁻¹' R))) ∧
          (∀ u, (G u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R) ∧
          (∀ u k l, (t.charts k).symm.trans
            ((G u).toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid V3) ∧
          (∀ x, new.map x = G 1 (data.initial.map x)) ∧ new.rim = data.initial.rim ∧
          HEq new.basepath data.initial.basepath ∧
          (∀ x : Rim, new.map x = data.initial.map x) ∧
          (w.right.trans Q) '' (new.map '' D ∩ (w.right.trans Q).source) ∩ J.space =
            H.map 1 '' P.space ∧
          (∀ v ∈ K₀.vertices, v ∈ interior J.space → (c v).2 = 0 →
            ∀ W : Set s.Carrier, IsOpen W → Q.symm v ∈ W →
              ∃ T : OpenPartialHomeomorph s.Carrier V3,
                Q.symm v ∈ T.source ∧ T (Q.symm v) = 0 ∧
                T.source ⊆ W ∩ (Q.source ∩ interior (s.projection ⁻¹' R)) ∧
                (∀ k, (s.charts k).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
                (step.projection ∘ step.inclusion) ⁻¹' T.source =
                  (w.left.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∪
                    (w.right.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∧
                (∀ y ∈ T.source,
                  y ∈ (step.projection ∘ step.inclusion) ''
                    (new.map '' D ∩ w.left.source) ↔ (c (T y)).1.1 = 0) ∧
                ∀ y ∈ T.source,
                  y ∈ (step.projection ∘ step.inclusion) ''
                    (new.map '' D ∩ w.right.source) ↔ (c (T y)).2 = 0) ∧
          ∃ (Z : SimplicialComplex ℝ (V2 × V2)) (E : SimplicialComplex ℝ V2)
            (first : Z.space ≃ₜ E.space),
            Z.faces.Finite ∧ E.faces.Finite ∧
            Z.space = {z | z.1 ∈ D ∧ z.2 ∈ D ∧
              step.projection (step.inclusion (new.map z.1)) =
                step.projection (step.inclusion (new.map z.2)) ∧ z.1 ≠ z.2} ∧
            E.space = {x | x ∈ D ∧ ∃ y ∈ D, x ≠ y ∧
              step.projection (step.inclusion (new.map x)) =
                step.projection (step.inclusion (new.map y))} ∧
            first.IsFinitePL ∧ first.symm.IsFinitePL ∧
            ∀ z : Z.space, (first z : V2) = z.val.1 := by
  classical
  let initial := data.initial
  have hop := data.exists_protected_link_sections_with_closed_support he hF hopen
  intro a b hab haint hpair U hU haU
  obtain ⟨w, c, Q, J, P, P₀, R₀, K, K₀, L, q, ρ, δ,
    ha, hb, haQ, hQzero, hQU, hQw, hQPL, _hbranches, hplane,
    hJ, hJQ, hzeroJ, hρ, hball, hclosed, hPs, hP₀s, hR₀, _hR₀J, hKR, hKs,
    _hqK, _hqi, hK₀K, hK₀s, _hqint, hwhole, holdcharts, happroach, hsections, hlinks,
    _hL, _hLs, _hδ, _hmargin, hmotions⟩ := hop a b hab haint hpair U hU haU
  refine ⟨w, c, Q, J, P, P₀, R₀, K, K₀, L, q, ρ, δ,
    ha, hb, haQ, hQzero, hQU, hQw, hQPL, _hbranches, hplane,
    hJ, hJQ, hzeroJ, hρ, hball, hclosed, hPs, hP₀s, hR₀, _hR₀J, hKR, hKs,
    _hqK, _hqi, hK₀K, hK₀s, _hqint, hwhole, holdcharts, happroach, hsections, hlinks,
    _hL, _hLs, _hδ, _hmargin, ?_⟩
  intro ε hε
  obtain ⟨H, hH, hsigns, _hzero, _hfaces, _hposition,
    Kamb, Knew, hKamb, hKambs, hKN, hKnews, hK₀N, _hqnew, _hqin,
    hincidence, _hnewlinks, G, new, hG, hGinv, hGzero, _hformula,
    hGout, _hGprotected, hGleft, hGfront, hGregion, _hGPL, hnewmap,
    hrim, hnewpath, _hrimpoint, hnewimage, relation⟩ := hmotions ε hε
  have hK : K.faces.Finite := hR₀.subset hKR
  have hKnew : Knew.faces.Finite := hKamb.subset hKN
  let p := step.projection ∘ step.inclusion
  have hleft (y : s.Carrier) (hy : y ∈ Q.source) :
      y ∈ p '' (new.map '' D ∩ w.left.source) ↔ (c (Q y)).2 = 0 := by
    rw [← hplane y hy]
    constructor
    · rintro ⟨z, ⟨⟨x, hx, rfl⟩, hxl⟩, hxy⟩
      have hfix : G 1 (new.map x) = new.map x := hGleft 1 hxl
      have heq : new.map x = initial.map x := (G 1).injective (hfix.trans (hnewmap x))
      exact ⟨initial.map x, ⟨mem_image_of_mem initial.map hx, heq ▸ hxl⟩, heq ▸ hxy⟩
    · rintro ⟨z, ⟨⟨x, hx, rfl⟩, hxl⟩, hxy⟩
      have heq : new.map x = initial.map x := (hnewmap x).trans (hGleft 1 hxl)
      exact ⟨new.map x, ⟨mem_image_of_mem new.map hx, heq.symm ▸ hxl⟩, heq.symm ▸ hxy⟩
  refine ⟨H, hH, hsigns, _hzero, _hfaces, _hposition,
    Kamb, Knew, hKamb, hKambs, hKN, hKnews, hK₀N, _hqnew, _hqin,
    hincidence, _hnewlinks, G, new, hG, hGinv, hGzero, _hformula,
    hGout, _hGprotected, hGleft, hGfront, hGregion, _hGPL, hnewmap,
    hrim, hnewpath, _hrimpoint, hnewimage, ?_, relation⟩
  intro v hv hvJ hvzero W hW hvW
  have hvK : v ∈ K.vertices := hK₀K hv
  have hvP₀ : v ∈ P₀.space := hK₀s.subset (K₀.vertices_subset_space hv)
  have hfix : H.map 1 v = v := H.fixed_protected 1 v hvP₀
  have hvN : v ∈ Knew.vertices := hK₀N hv
  have hvA : v ∈ Kamb.vertices := hKN hvN
  have hlinknew : (Knew.link v).space = H.map 1 '' (K.link v).space := by
    simpa only [hfix] using (hincidence v hvK).1
  obtain ⟨n, oldP, holdPi, holdP, holdPs⟩ := hlinks v hvK hvJ
  obtain ⟨hzeros, hpos, hneg⟩ := hsections v hv hvJ hvzero
  let E : V3 ≃ᴬ[ℝ] C3 :=
    c.toLinearEquiv.toAffineEquiv.toContinuousAffineEquiv.trans
      (ContinuousAffineEquiv.constVAdd ℝ C3 (-c v))
  have hEv : E v = 0 := by change -c v + c v = 0; exact neg_add_cancel _
  have hEheight (x : V3) : (E x).2 = (c x).2 := by
    change -(c v).2 + (c x).2 = (c x).2
    rw [hvzero, neg_zero, zero_add]
  let A : V3 →ᵃ[ℝ] ℝ := ((LinearMap.snd ℝ (ℝ × ℝ) ℝ).comp c.toLinearMap).toAffineMap
  let B : C3 →ᵃ[ℝ] ℝ := (LinearMap.snd ℝ (ℝ × ℝ) ℝ).toAffineMap
  let f₁ : V3 → C3 := E ∘ H.map 1
  have hf₁ : (K.link v).AffineOnFaces f₁ := by
    intro face hface
    obtain ⟨a, ha⟩ := hH face (hKR hface.1)
    exact ⟨E.toContinuousAffineMap.comp a, fun x hx => congrArg E (ha hx)⟩
  have hfi : Function.Injective f₁ := E.injective.comp (H.map 1).injective
  have hpositive (x : V3) (hx : x ∈ (K.link v).vertices) (hp : 0 < A x) :
      0 < B (f₁ x) := by
    change 0 < (E (H.map 1 x)).2
    rw [hEheight]
    exact ((hsigns x (hKR hx.1) hp.ne' 1).1).mpr hp
  have hnegative (x : V3) (hx : x ∈ (K.link v).vertices) (hn : A x < 0) :
      B (f₁ x) < 0 := by
    change (E (H.map 1 x)).2 < 0
    rw [hEheight]
    exact ((hsigns x (hKR hx.1) hn.ne 1).2).mpr hn
  obtain ⟨m, Pnew, a₀, b₀, hPi, hP, hPimage, hab₀, hPzero, _, _, _⟩ :=
    exists_repaired_crossed_link_bands (K.link v) (finite_link_faces hK v)
      oldP holdP holdPi holdPs hf₁ hfi.injOn A B hpositive hnegative hzeros hneg hpos
  have new_positive (A : V3 →ᵃ[ℝ] ℝ) (B : C3 →ᵃ[ℝ] ℝ)
      (hsign : ∀ x ∈ (K.link v).vertices, 0 < A x → 0 < B (f₁ x))
      (hpoint : ∃ x ∈ (K.link v).space, 0 < A x) :
      ∃ y ∈ Pnew.boundary ℝ, 0 < B y := by
    obtain ⟨x, hx, hxpos⟩ := hpoint
    obtain ⟨face, hface, hxface⟩ := mem_space_iff.mp hx
    have hex : ∃ u ∈ face, 0 < A u := by
      by_contra h
      push Not at h
      have hbound : convexHull ℝ (face : Set V3) ⊆ {z | A z ≤ 0} :=
        convexHull_min h ((convex_Iic (0 : ℝ)).affine_preimage A)
      exact hxpos.not_ge (hbound hxface)
    obtain ⟨u, hu, hupos⟩ := hex
    have huK := (K.link v).face_subset_vertices hface hu
    refine ⟨f₁ u, hPimage.symm.subset ?_, hsign u huK hupos⟩
    exact mem_image_of_mem f₁ ((K.link v).vertices_subset_space huK)
  have hPpos : ∃ x ∈ Pnew.boundary ℝ, x.2 > 0 := new_positive A B hpositive hpos
  have hPneg : ∃ x ∈ Pnew.boundary ℝ, x.2 < 0 := by
    have hnegA : ∃ x ∈ (K.link v).space, A x < 0 := hneg
    obtain ⟨x, hx, hxn⟩ := new_positive (-A) (-B)
      (fun x hx hp => neg_pos.mpr (hnegative x hx (neg_pos.mp hp)))
      (by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using hnegA)
    refine ⟨x, hx, ?_⟩
    change 0 < -x.2 at hxn
    exact neg_pos.mp hxn
  have hEA := Kamb.affineOnFaces_affine E.toContinuousAffineMap
  have hEN := Knew.affineOnFaces_affine E.toContinuousAffineMap
  let Ambient := hEA.embeddedImage E.injective.injOn
  let Branch := hEN.embeddedImage E.injective.injOn
  have hAmbient : Ambient.faces.Finite := hEA.embeddedImage_finite E.injective.injOn hKamb
  have hBranch : Branch.faces.Finite := hEN.embeddedImage_finite E.injective.injOn hKnew
  have hAmbientS : Ambient.space = E '' Kamb.space := hEA.embeddedImage_space _
  have hBranchS : Branch.space = E '' Knew.space := hEN.embeddedImage_space _
  have hBA : Branch ≤ Ambient := by
    have hfacesN : Branch.faces = (fun face => face.image E) '' Knew.faces :=
      hEN.embeddedImage_faces E.injective.injOn
    have hfacesA : Ambient.faces = (fun face => face.image E) '' Kamb.faces :=
      hEA.embeddedImage_faces E.injective.injOn
    intro face hface
    change face ∈ Branch.faces at hface
    change face ∈ Ambient.faces
    rw [hfacesN] at hface
    rw [hfacesA]
    obtain ⟨u, hu, rfl⟩ := hface
    exact ⟨u, hKN hu, rfl⟩
  have hzeroA : (0 : C3) ∈ Ambient.vertices := by
    have heq : Ambient.vertices = E '' Kamb.vertices :=
      hEA.embeddedImage_vertices E.injective.injOn
    exact heq.symm.subset ⟨v, hvA, hEv⟩
  have hzeroB : (0 : C3) ∈ Branch.vertices := by
    have heq : Branch.vertices = E '' Knew.vertices :=
      hEN.embeddedImage_vertices E.injective.injOn
    exact heq.symm.subset ⟨v, hvN, hEv⟩
  have hintA : (0 : C3) ∈ interior Ambient.space := by
    rw [hAmbientS, hKambs]
    change (0 : C3) ∈ interior (E.toHomeomorph '' J.space)
    rw [← E.toHomeomorph.image_interior]
    exact ⟨v, hvJ, hEv⟩
  have hPlink : Pnew.boundary ℝ = (Branch.link 0).space := by
    have h := hEN.embeddedImage_link_space E.injective.injOn hvN
    change (Branch.link (E v)).space = E '' (Knew.link v).space at h
    rw [hEv, hlinknew, image_image] at h
    exact hPimage.trans h.symm
  have hPambient : Pnew.boundary ℝ ⊆ (Ambient.link 0).space := by
    rw [hPlink]
    apply space_subset_of_le
    intro face hface
    exact ⟨hBA hface.1, hface.2.1, hBA hface.2.2⟩
  obtain ⟨C, g, h, boundary, _hC, _hcv, _hC0, hh, _hboundary,
    hhg, hgzero, _hbase, _hray, _hrim, hflat, _hside, hcone⟩ :=
    exists_original_crossed_star Ambient hAmbient hzeroA hintA Pnew hP hPi
      hPambient hab₀ hPzero hPneg hPpos
  obtain ⟨χ, hχsource, _hχtarget, hχ, _hχinv, _hχfinite, _hχifinite, hχval, _hχival⟩ :=
    hh.exists_interior_chart rfl
  have hstarint : (0 : C3) ∈ interior (Ambient.closedStar 0).space := by
    obtain ⟨d, hd, hnear⟩ := Ambient.exists_ball_inter_space_subset_closedStar hAmbient hzeroA
    apply interior_maximal (fun x hx => hnear ⟨interior_subset hx.1, hx.2⟩)
      (isOpen_interior.inter isOpen_ball)
    exact ⟨hintA, mem_ball_self hd⟩
  have hχzero : (0 : C3) ∈ χ.source := hχsource.symm.subset hstarint
  have hχcenter : χ 0 = 0 :=
    (hχval ⟨0, interior_subset hstarint⟩).trans ((hhg _).trans hgzero)
  obtain ⟨d, hd, hnear⟩ := Branch.exists_ball_inter_space_subset_closedStar hBranch hzeroB
  have hbranchCone : (Branch.closedStar 0).space = convexJoin ℝ {0} (Pnew.boundary ℝ) := by
    have hne : (Branch.link 0).space.Nonempty :=
      ⟨a₀, hPlink.subset (hPzero.symm.subset (by simp)).1⟩
    rw [hPlink, ← coneAtZero_link_eq_closedStar Branch hzeroB]
    exact (Branch.link 0).coneAtZero_space_eq_convexJoin
      (fun _ hs => linearIndependent_of_mem_link_zero hs) Branch.injOn_normalize_link hne
  let V := interior J.space ∩ (Q.target ∩ Q.symm ⁻¹' W)
  have hV : IsOpen V := isOpen_interior.inter (Q.symm.isOpen_inter_preimage hW)
  have hvV : v ∈ V := ⟨hvJ, hJQ (interior_subset hvJ), hvW⟩
  let O := ball (0 : C3) d ∩ E '' V
  have hO : IsOpen O := isOpen_ball.inter (E.toHomeomorph.isOpenMap _ hV)
  let localChart := E.toHomeomorph.toOpenPartialHomeomorph.trans (χ.restrOpen O hO)
  have hvLocal : v ∈ localChart.source := by
    refine ⟨mem_univ _, ?_, ?_, mem_image_of_mem E hvV⟩
    · change E v ∈ χ.source
      rw [hEv]
      exact hχzero
    · change E v ∈ ball 0 d
      rw [hEv]
      exact mem_ball_self hd
  have hLocalPL : LocallyPiecewiseAffineOn localChart localChart.source :=
    (hχ.comp (locallyPiecewiseAffineOn_affine E.toContinuousAffineMap isOpen_univ)).mono
      localChart.open_source (fun _ hx => ⟨hx.1, hx.2.1⟩)
  have hlocal (x : V3) (hx : x ∈ localChart.source) :
      x ∈ V ∧ ((c x).2 = 0 ↔ (localChart x).1.1 = 0) ∧
        (x ∈ Knew.space ↔ (localChart x).2 = 0) := by
    have hxV : x ∈ V := by
      obtain ⟨y, hy, heq⟩ := hx.2.2.2
      exact E.injective heq ▸ hy
    have hxstar : E x ∈ (Ambient.closedStar 0).space :=
      interior_subset (hχsource.subset hx.2.1)
    have hvalue : localChart x = h ⟨E x, hxstar⟩ := hχval ⟨E x, hxstar⟩
    have hBmem : E x ∈ Branch.space ↔ x ∈ Knew.space := by
      rw [hBranchS]
      exact E.injective.mem_set_image
    have hBstar : E x ∈ Branch.space ↔ E x ∈ (Branch.closedStar 0).space :=
      ⟨fun h => hnear ⟨h, hx.2.2.1⟩,
        fun h => space_subset_of_le
          (show Branch.closedStar 0 ≤ Branch from fun _ hs => hs.1) h⟩
    refine ⟨hxV, ?_, ?_⟩
    · rw [← hEheight, hvalue]
      exact hflat ⟨E x, hxstar⟩
    · rw [← hBmem, hBstar, hbranchCone, hvalue]
      exact hcone ⟨E x, hxstar⟩
  let coord := localChart.trans c.symm.toHomeomorph.toOpenPartialHomeomorph
  let T := Q.trans coord
  have hvT : Q.symm v ∈ T.source := by
    refine ⟨Q.map_target (hJQ (interior_subset hvJ)), ?_, mem_univ _⟩
    change Q (Q.symm v) ∈ localChart.source
    rw [Q.right_inv (hJQ (interior_subset hvJ))]
    exact hvLocal
  have hvalue (y : s.Carrier) : c (T y) = localChart (Q y) := c.apply_symm_apply _
  have hTPL (k : s.Index) : (s.charts k).symm.trans T ∈ piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    have hf := (locallyPiecewiseAffineOn_affine
      c.symm.toContinuousLinearMap.toContinuousAffineMap isOpen_univ).comp hLocalPL
    exact (hf.comp (hQPL k).1).mono ((s.charts k).symm.trans T).open_source
      (fun z hz => ⟨⟨hz.1, hz.2.1⟩, hz.2.2.1, mem_univ _⟩)
  have hsource (y : s.Carrier) (hy : y ∈ T.source) :
      y ∈ W ∩ (Q.source ∩ interior (s.projection ⁻¹' R)) := by
    have hV := (hlocal (Q y) hy.2.1).1
    have hyW : y ∈ W := by
      have h := hV.2.2
      change Q.symm (Q y) ∈ W at h
      rwa [Q.left_inv hy.1] at h
    exact ⟨hyW, hy.1, (hQU hy.1).2⟩
  refine ⟨T, hvT, ?_, hsource, hTPL, ?_, ?_, ?_⟩
  · change c.symm (χ (E (Q (Q.symm v)))) = 0
    rw [Q.right_inv (hJQ (interior_subset hvJ)), hEv, hχcenter, map_zero]
  · ext x
    constructor
    · intro hx
      rcases w.whole_preimage.subset (hQw (hsource _ hx).2.1) with hl | hr
      · exact Or.inl ⟨hl, hx⟩
      · exact Or.inr ⟨hr, hx⟩
    · exact fun hx => hx.elim And.right And.right
  · intro y hy
    rw [hleft y hy.1, hvalue]
    exact (hlocal (Q y) hy.2.1).2.1
  · intro y hy
    have hyJ := interior_subset (hlocal (Q y) hy.2.1).1.1
    have hright : y ∈ p '' (new.map '' D ∩ w.right.source) ↔ Q y ∈ Knew.space := by
      rw [hKnews, ← hnewimage]
      constructor
      · rintro ⟨x, ⟨hxD, hxw⟩, hxy⟩
        refine ⟨⟨x, ⟨hxD, hxw, ?_⟩, ?_⟩, hyJ⟩
        · change w.right x ∈ Q.source
          rw [congrFun w.right_eq x]
          change p x ∈ Q.source
          rw [hxy]
          exact hy.1
        · change Q (w.right x) = Q y
          rw [congrFun w.right_eq x]
          exact congrArg Q hxy
      · rintro ⟨⟨x, ⟨hxD, hxT⟩, hxy⟩, _⟩
        refine ⟨x, ⟨hxD, hxT.1⟩, ?_⟩
        have hxQ : w.right x ∈ Q.source := hxT.2
        rw [congrFun w.right_eq x] at hxQ
        apply Q.injOn hxQ hy.1
        change Q (w.right x) = Q y at hxy
        rw [congrFun w.right_eq x] at hxy
        exact hxy
    rw [hright, hvalue]
    exact (hlocal (Q y) hy.2.1).2.2

theorem OriginalGeneralPositionData.exists_protected_crossed_charts
    {s t : Stage e S f r C} {step : Step s t} {R Fmark : Set M}
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    {old : StageMarkedDisk t R Fmark base Jgroup}
    (data : OriginalGeneralPositionData step old)
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark)) :
  ∀ a b : D, a ≠ b → (a : V2) ∉ Rim →
    step.projection (step.inclusion (data.initial.map a)) =
      step.projection (step.inclusion (data.initial.map b)) →
    ∀ U : Set s.Carrier, IsOpen U →
      step.projection (step.inclusion (data.initial.map a)) ∈ U →
      ∃ (w : TwoBranchWindow (step.projection ∘ step.inclusion))
        (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3)
        (J P P₀ R₀ K K₀ L : SimplicialComplex ℝ V3)
        (q : V3 → ℝ × ℝ) (ρ δ : ℝ),
        data.initial.map a ∈ w.left.source ∧ data.initial.map b ∈ w.right.source ∧
        step.projection (step.inclusion (data.initial.map a)) ∈ Q.source ∧
        Q (step.projection (step.inclusion (data.initial.map a))) = 0 ∧
        Q.source ⊆ U ∩ interior (s.projection ⁻¹' R) ∧ Q.source ⊆ w.target ∧
        (∀ k, (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
        (∀ k, (t.charts k).symm.trans (w.left.trans Q) ∈ piecewiseAffineGroupoid V3 ∧
          (t.charts k).symm.trans (w.right.trans Q) ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ Q.source,
          y ∈ (step.projection ∘ step.inclusion) '' (data.initial.map '' D ∩ w.left.source) ↔
            (c (Q y)).2 = 0) ∧
        J.faces.Finite ∧ J.space ⊆ Q.target ∧ (0 : V3) ∈ interior J.space ∧
        0 < ρ ∧ ball (0 : V3) ρ ⊆ interior J.space ∧
        P.space = (w.right.trans Q) ''
          (data.initial.map '' D ∩ (w.right.trans Q).source) ∩ J.space ∧
        P₀.space = P.space \ ball (0 : V3) ρ ∧
        R₀.faces.Finite ∧ R₀.IsSubdivision J ∧ K ≤ R₀ ∧ K.space = P.space ∧
        K.AffineOnFaces q ∧ InjOn q K.space ∧ K₀ ≤ K ∧ K₀.space = P₀.space ∧
        (∀ z ∈ P.space, z ∈ interior J.space → q z ∈ interior (q '' P.space)) ∧
        (step.projection ∘ step.inclusion) ⁻¹' (Q.symm '' J.space) =
          (w.left.trans Q).symm '' J.space ∪ (w.right.trans Q).symm '' J.space ∧
        (∀ v ∈ P₀.space, v ∈ interior J.space → (c v).2 = 0 →
          ∃ T : OpenPartialHomeomorph V3 C3,
            (0 : V3) ∈ T.source ∧ T 0 = 0 ∧
            LocallyPiecewiseAffineOn T.symm T.target ∧
            (∀ z ∈ T.source, z ∈ (fun x : V3 => -v + x) '' K.space ↔
              (T z).1.1 = 0) ∧
            ∀ z ∈ T.source, (c z).2 = 0 ↔ (T z).2 = 0) ∧
        (∀ v ∈ P₀.space, v ∈ interior J.space → (c v).2 = 0 →
          v ∈ closure (K.space ∩ {z | 0 < (c z).2}) ∧
          v ∈ closure (K.space ∩ {z | (c z).2 < 0})) ∧
        (∀ v ∈ K₀.vertices, v ∈ interior J.space → (c v).2 = 0 →
          ((K.link v).space ∩ {z | (c z).2 = 0}).ncard = 2 ∧
          (∃ z ∈ (K.link v).space, 0 < (c z).2) ∧
          ∃ z ∈ (K.link v).space, (c z).2 < 0) ∧
        (∀ v ∈ K.vertices, v ∈ interior J.space →
          ∃ (n : ℕ) (T : Polygon V3 (n + 3)), Function.Injective T ∧
            T.HasSimplicialEdges ∧ T.boundary ℝ = (K.link v).space) ∧
        L.faces.Finite ∧ L.space = J.space ∩ {z | (c z).2 = 0} ∧
        0 < δ ∧ (∀ v ∈ R₀.vertices, (c v).2 ≠ 0 → δ ≤ |(c v).2|) ∧
        ∀ ε : ℝ, 0 < ε → ∃ H : PLCarrierMotion J.space P₀.space ε,
          R₀.AffineOnFaces (H.map 1) ∧
          (∀ v ∈ R₀.vertices, (c v).2 ≠ 0 → ∀ u,
            (0 < (c (H.map u v)).2 ↔ 0 < (c v).2) ∧
            ((c (H.map u v)).2 < 0 ↔ (c v).2 < 0)) ∧
          (∀ v ∈ K.vertices,
            (c (H.map 1 v)).2 = 0 ↔ v ∈ K₀.vertices ∧ (c v).2 = 0) ∧
          (∀ face ∈ K.faces, (∀ v ∈ face, (c (H.map 1 v)).2 = 0) ↔
            face ∈ K₀.faces ∧ ∀ v ∈ face, (c v).2 = 0) ∧
          (∀ face ∈ K.faces, face ∉ K₀.faces → ∀ other ∈ L.faces,
            affineSpan ℝ (H.map 1 '' (face : Set V3) ∪ (other : Set V3)) = ⊤ ∨
              Disjoint (intrinsicInterior ℝ (convexHull ℝ (H.map 1 '' (face : Set V3))))
                (convexHull ℝ (other : Set V3))) ∧
          ∃ Kamb Knew : SimplicialComplex ℝ V3,
            Kamb.faces.Finite ∧ Kamb.space = J.space ∧ Knew ≤ Kamb ∧
            Knew.space = H.map 1 '' P.space ∧ K₀ ≤ Knew ∧
            Knew.AffineOnFaces (q ∘ (H.map 1).symm) ∧
            InjOn (q ∘ (H.map 1).symm) Knew.space ∧
            (∀ v ∈ K.vertices,
              (Knew.link (H.map 1 v)).space = H.map 1 '' (K.link v).space ∧
              (Knew.closedStar (H.map 1 v)).space = H.map 1 '' (K.closedStar v).space) ∧
            (∀ v ∈ K.vertices, v ∈ interior J.space →
              ∃ (n : ℕ) (T : Polygon V3 (n + 3)), Function.Injective T ∧
                T.HasSimplicialEdges ∧ T.boundary ℝ = (Knew.link (H.map 1 v)).space) ∧
          ∃ (G : I → t.Carrier ≃ₜ t.Carrier)
            (new : StageMarkedDisk t R Fmark base Jgroup),
          Continuous (fun z : I × t.Carrier => G z.1 z.2) ∧
          Continuous (fun z : I × t.Carrier => (G z.1).symm z.2) ∧
          (∀ x, G 0 x = x) ∧
          (∀ u, EqOn (G u)
            ((w.right.trans Q).symm ∘ H.map u ∘ (w.right.trans Q))
              (w.right.trans Q).source) ∧
          (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' J.space)ᶜ) ∧
          (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' P₀.space)) ∧
          (∀ u, EqOn (G u) id w.left.source) ∧
          (∀ u, EqOn (G u) id (frontier (t.projection ⁻¹' R))) ∧
          (∀ u, (G u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R) ∧
          (∀ u k l, (t.charts k).symm.trans
            ((G u).toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid V3) ∧
          (∀ x, new.map x = G 1 (data.initial.map x)) ∧ new.rim = data.initial.rim ∧
          HEq new.basepath data.initial.basepath ∧
          (∀ x : Rim, new.map x = data.initial.map x) ∧
          (w.right.trans Q) '' (new.map '' D ∩ (w.right.trans Q).source) ∩ J.space =
            H.map 1 '' P.space ∧
          (∀ v ∈ K₀.vertices, v ∈ interior J.space → (c v).2 = 0 →
            ∀ W : Set s.Carrier, IsOpen W → Q.symm v ∈ W →
              ∃ T : OpenPartialHomeomorph s.Carrier V3,
                Q.symm v ∈ T.source ∧ T (Q.symm v) = 0 ∧
                T.source ⊆ W ∩ (Q.source ∩ interior (s.projection ⁻¹' R)) ∧
                (∀ k, (s.charts k).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
                (step.projection ∘ step.inclusion) ⁻¹' T.source =
                  (w.left.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∪
                    (w.right.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∧
                (∀ y ∈ T.source,
                  y ∈ (step.projection ∘ step.inclusion) ''
                    (new.map '' D ∩ w.left.source) ↔ (c (T y)).1.1 = 0) ∧
                ∀ y ∈ T.source,
                  y ∈ (step.projection ∘ step.inclusion) ''
                    (new.map '' D ∩ w.right.source) ↔ (c (T y)).2 = 0) ∧
          ∃ (Z : SimplicialComplex ℝ (V2 × V2)) (E : SimplicialComplex ℝ V2)
            (first : Z.space ≃ₜ E.space),
            Z.faces.Finite ∧ E.faces.Finite ∧
            Z.space = {z | z.1 ∈ D ∧ z.2 ∈ D ∧
              step.projection (step.inclusion (new.map z.1)) =
                step.projection (step.inclusion (new.map z.2)) ∧ z.1 ≠ z.2} ∧
            E.space = {x | x ∈ D ∧ ∃ y ∈ D, x ≠ y ∧
              step.projection (step.inclusion (new.map x)) =
                step.projection (step.inclusion (new.map y))} ∧
            first.IsFinitePL ∧ first.symm.IsFinitePL ∧
            ∀ z : Z.space, (first z : V2) = z.val.1 := by
  classical
  intro a b hab haint hpair U hU haU
  obtain ⟨w, c, Q, J, P, P₀, R₀, K, K₀, L, q, ρ, δ, h⟩ :=
    data.exists_protected_crossed_charts_with_closed_support he hF hopen
      a b hab haint hpair U hU haU
  refine ⟨w, c, Q, J, P, P₀, R₀, K, K₀, L, q, ρ, δ, ?_⟩
  rcases h with ⟨ha, hb, haQ, hQzero, hQU, hQw, hQPL, hbranches, hplane,
    hJ, hJQ, hzeroJ, hρ, hball, _hclosed, hrest⟩
  exact ⟨ha, hb, haQ, hQzero, hQU, hQw, hQPL, hbranches, hplane,
    hJ, hJQ, hzeroJ, hρ, hball, hrest⟩

end Geometry.OriginalPLTower
