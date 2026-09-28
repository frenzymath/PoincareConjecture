import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.OriginalGeneralPositionCrossings
import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcSurgeryCrossings
import PoincareConjecture.Proofs.M76.Wall.Mathlib.TwoRayStraightening
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineProd












set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex Topology unitInterval
open scoped BigOperators
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


theorem OriginalGeneralPositionData.exists_protected_edge_crossed_charts_with_closed_support
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
            J.faces.Finite ∧ J.space ⊆ Q.target ∧
            (0 : V3) ∈ interior J.space ∧ 0 < ρ ∧ ball (0 : V3) ρ ⊆ interior J.space ∧
            closedBall (0 : V3) ρ ⊆ interior J.space ∧
            P.space = (w.right.trans Q) ''
              (data.initial.map '' D ∩ (w.right.trans Q).source) ∩ J.space ∧
            P₀.space = P.space \ ball (0 : V3) ρ ∧ K.faces.Finite ∧ K.space = P.space ∧
            R₀.faces.Finite ∧ R₀.IsSubdivision J ∧ K ≤ R₀ ∧
            K.AffineOnFaces q ∧ InjOn q K.space ∧ K₀ ≤ K ∧ K₀.space = P₀.space ∧
            (∀ z ∈ K.space, z ∈ interior J.space → q z ∈ interior (q '' K.space)) ∧
            (step.projection ∘ step.inclusion) ⁻¹' (Q.symm '' J.space) =
              (w.left.trans Q).symm '' J.space ∪ (w.right.trans Q).symm '' J.space ∧
            L.faces.Finite ∧ L.space = J.space ∩ {z | (c z).2 = 0} ∧
            0 < δ ∧ (∀ v ∈ R₀.vertices, (c v).2 ≠ 0 → δ ≤ |(c v).2|) ∧
            (∀ v ∈ P₀.space, v ∈ interior J.space → (c v).2 = 0 →
              ∃ T : OpenPartialHomeomorph V3 C3,
                (0 : V3) ∈ T.source ∧ T 0 = 0 ∧
                LocallyPiecewiseAffineOn T.symm T.target ∧
                (∀ z ∈ T.source, z ∈ (fun x : V3 => -v + x) '' K.space ↔
                  (T z).1.1 = 0) ∧
                ∀ z ∈ T.source, (c z).2 = 0 ↔ (T z).2 = 0) ∧
            (∀ z ∈ P₀.space, z ∈ interior J.space → (c z).2 = 0 →
              z ∈ closure (K.space ∩ {x | 0 < (c x).2}) ∧
              z ∈ closure (K.space ∩ {x | (c x).2 < 0})) ∧
            ∀ ε : ℝ, 0 < ε → ∃ H : PLCarrierMotion J.space P₀.space ε,
              K.AffineOnFaces (H.map 1) ∧
              (∀ v ∈ K.vertices, (c v).2 ≠ 0 → ∀ u,
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
                (∀ y ∈ Q.source,
                  y ∈ (step.projection ∘ step.inclusion) ''
                    (new.map '' D ∩ w.left.source) ↔ (c (Q y)).2 = 0) ∧
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
                (∀ edge ∈ K₀.faces, edge.card = 2 → (∀ v ∈ edge, (c v).2 = 0) →
                  ∀ z ∈ intrinsicInterior ℝ (convexHull ℝ (edge : Set V3)),
                    z ∈ interior J.space → ∀ W : Set s.Carrier,
                      IsOpen W → Q.symm z ∈ W → ∃ T : OpenPartialHomeomorph s.Carrier V3,
                        Q.symm z ∈ T.source ∧ T (Q.symm z) = 0 ∧
                        T.source ⊆ W ∩ (Q.source ∩ interior (s.projection ⁻¹' R)) ∧
                        (∀ k, (s.charts k).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
                        (step.projection ∘ step.inclusion) ⁻¹' T.source =
                          (w.left.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∪
                            (w.right.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∧
                        (∀ y ∈ T.source,
                          y ∈ (step.projection ∘ step.inclusion) ''
                            (new.map '' D ∩ w.left.source) ↔ (c (T y)).2 = 0) ∧
                        ∀ y ∈ T.source,
                          y ∈ (step.projection ∘ step.inclusion) ''
                            (new.map '' D ∩ w.right.source) ↔ (c (T y)).1.1 = 0) ∧
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
  have hop := data.exists_protected_crossed_charts_with_closed_support he hF hopen
  intro a b hab haint hpair U hU haU
  obtain ⟨w, c, Q, J, P, P₀, R₀, K, K₀, L, q, ρ, δ,
    ha, hb, haQ, hQzero, hQU, hQw, hQPL, hbranches, hplane,
    hJ, hJQ, hzeroJ, hρ, hball, hclosed, hPs, hP₀s, hR₀, hR₀J, hKR, hKs,
    hqK, hqi, hK₀K, hK₀s, hqint, hwhole, holdcharts, happroach,
    _hsections, _hlinks, hL, hLs, hδ, hmargin, hmotions⟩ :=
    hop a b hab haint hpair U hU haU
  have hK : K.faces.Finite := hR₀.subset hKR
  have hparam (z : V3) (hz : z ∈ K.space) (hzJ : z ∈ interior J.space) :
      q z ∈ interior (q '' K.space) := by
    rw [hKs]
    exact hqint z (hKs.subset hz) hzJ
  refine ⟨w, c, Q, J, P, P₀, R₀, K, K₀, L, q, ρ, δ,
    ha, hb, haQ, hQzero, hQU, hQw, hQPL, hbranches, hJ, hJQ, hzeroJ,
    hρ, hball, hclosed, hPs, hP₀s, hK, hKs, hR₀, hR₀J, hKR, hqK, hqi, hK₀K,
    hK₀s, hparam, hwhole, hL, hLs, hδ, hmargin, holdcharts,
    happroach, ?_⟩
  intro ε hε
  obtain ⟨H, hH, hsigns, hzeroVertices, hfaces, hposition,
    Kamb, Knew, hKamb, hKambs, hKN, hKnews, hK₀N, hqnew, hqin,
    hincidence, hnewlinks, G, new, hG, hGinv, hGzero, hformula,
    hGout, hGprotected, hGleft, hGfront, hGregion, hGPL, hnewmap,
    hrim, hnewpath, hrimpoint, hnewimage, hvertexcharts, relation⟩ := hmotions ε hε
  have hHK : K.AffineOnFaces (H.map 1) := fun face hf => hH face (hKR hf)
  have hHi : InjOn (H.map 1) K.space := (H.map 1).injective.injOn
  let N := hHK.embeddedImage hHi
  have hNs : N.space = H.map 1 '' K.space := hHK.embeddedImage_space hHi
  let ell : V3 →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap
  let p := step.projection ∘ step.inclusion
  have hleft (y : s.Carrier) (hy : y ∈ Q.source) :
      y ∈ p '' (new.map '' D ∩ w.left.source) ↔ ell (Q y) = 0 := by
    change y ∈ p '' (new.map '' D ∩ w.left.source) ↔ (c (Q y)).2 = 0
    rw [← hplane y hy]
    constructor
    · rintro ⟨z, ⟨⟨x, hx, rfl⟩, hxl⟩, hxy⟩
      have hfix : G 1 (new.map x) = new.map x := hGleft 1 hxl
      have heq : new.map x = initial.map x := (G 1).injective (hfix.trans (hnewmap x))
      exact ⟨initial.map x, ⟨mem_image_of_mem initial.map hx, heq ▸ hxl⟩, heq ▸ hxy⟩
    · rintro ⟨z, ⟨⟨x, hx, rfl⟩, hxl⟩, hxy⟩
      have heq : new.map x = initial.map x := (hnewmap x).trans (hGleft 1 hxl)
      exact ⟨new.map x, ⟨mem_image_of_mem new.map hx, heq.symm ▸ hxl⟩, heq.symm ▸ hxy⟩
  refine ⟨H, hHK, fun v hv => hsigns v (hKR hv), hzeroVertices, hfaces, hposition,
    Kamb, Knew, hKamb, hKambs, hKN, hKnews, hK₀N, hqnew, hqin,
    hincidence, hnewlinks,
    G, new, hG, hGinv, hGzero, hformula, hGout, hGprotected, hGleft, hGfront,
    hGregion, hGPL, hnewmap, hrim, hnewpath, hrimpoint, hnewimage,
    hleft, hvertexcharts, ?_, relation⟩
  intro edge hedge he2 hezero z hzedge hzJ W hW hzW
  have heK : edge ∈ K.faces := hK₀K hedge
  have hzP₀ : z ∈ P₀.space := hK₀s.subset
    (K₀.convexHull_subset_space hedge (intrinsicInterior_subset hzedge))
  have hzK : z ∈ K.space := K.convexHull_subset_space heK (intrinsicInterior_subset hzedge)
  have hzeroHull : convexHull ℝ (edge : Set V3) ⊆ {x | ell x = 0} :=
    convexHull_min hezero ((convex_singleton (0 : ℝ)).linear_preimage ell.toLinearMap)
  have hz0 : ell z = 0 := hzeroHull (intrinsicInterior_subset hzedge)
  have hfix (x : V3) (hx : x ∈ convexHull ℝ (edge : Set V3)) : H.map 1 x = x :=
    H.fixed_protected 1 x (hK₀s.subset (K₀.convexHull_subset_space hedge hx))
  have hzfix : H.map 1 z = z := hfix z (intrinsicInterior_subset hzedge)
  let Kq := hqK.embeddedImage hqi
  have hKq : Kq.faces.Finite := hqK.embeddedImage_finite hqi hK
  have heq : edge.image q ∈ Kq.faces :=
    (hqK.image_mem_embeddedImage_iff hqi (K.subset_space heK)).mpr heK
  have heqcard : (edge.image q).card = Module.finrank ℝ (ℝ × ℝ) := by
    rw [Finset.card_image_iff.mpr (hqi.mono (K.subset_space heK)), he2]
    simp [Module.finrank_prod]
  have hzq : q z ∈ convexHull ℝ (edge.image q : Set (ℝ × ℝ)) := by
    rw [Finset.coe_image, ← hqK.image_convexHull heK]
    exact mem_image_of_mem q (intrinsicInterior_subset hzedge)
  have hzqint : q z ∈ interior Kq.space := by
    rw [hqK.embeddedImage_space hqi]
    exact hparam z hzK hzJ
  have hcount := Kq.faceLink_ncard_eq_two_of_hull_meets_interior hKq heq heqcard
    ⟨q z, hzq, hzqint⟩
  rw [hqK.ncard_embeddedImage_faceLink hqi heK,
    K.ncard_faceLink_vertices_eq_cofaces, he2] at hcount
  obtain ⟨a₀, b₀, _hab₀, hset⟩ := ncard_eq_two.mp hcount
  have ha₀ : a₀ ∈ K.faces ∧ a₀.card = 3 ∧ edge ⊆ a₀ := by
    change a₀ ∈ {face | face ∈ K.faces ∧ face.card = 3 ∧ edge ⊆ face}
    rw [hset]
    exact Or.inl rfl
  have hb₀ : b₀ ∈ K.faces ∧ b₀.card = 3 ∧ edge ⊆ b₀ := by
    change b₀ ∈ {face | face ∈ K.faces ∧ face.card = 3 ∧ edge ⊆ face}
    rw [hset]
    exact Or.inr rfl
  have hexhaust (face : Finset V3) (hf : face ∈ K.faces) (hef : edge ⊆ face) :
      face ⊆ a₀ ∨ face ⊆ b₀ := by
    have hhi : face.card ≤ 3 := by
      simpa [Module.finrank_prod] using hqK.face_card_le_of_injOn hqi hf
    have hlo := Finset.card_le_card hef
    by_cases htwo : face.card = 2
    · have he : edge = face := Finset.eq_of_subset_of_card_le hef (by omega)
      exact Or.inl (he ▸ ha₀.2.2)
    · have hmem : face ∈ {f | f ∈ K.faces ∧ f.card = 3 ∧ edge ⊆ f} :=
        ⟨hf, by omega, hef⟩
      rw [hset] at hmem
      exact hmem.elim (fun h => Or.inl (h ▸ Finset.Subset.rfl))
        (fun h => Or.inr (h ▸ Finset.Subset.rfl))
  obtain ⟨V, hV, hzV, hgerm⟩ := K.exists_open_two_coface_carrier_germ hK
    heK ha₀.1 hb₀.1 hexhaust hzedge
  obtain ⟨u₀, _hu₀, hua⟩ := Finset.exists_eq_insert_iff.mpr ⟨ha₀.2.2, by omega⟩
  obtain ⟨v₀, _hv₀, hvb⟩ := Finset.exists_eq_insert_iff.mpr ⟨hb₀.2.2, by omega⟩
  obtain ⟨hpositive, hnegative⟩ := happroach z hzP₀ hzJ hz0
  have signed (L : V3 →L[ℝ] ℝ) (heL : ∀ x ∈ edge, L x = 0)
      (hcl : z ∈ closure (K.space ∩ {x | 0 < L x})) :
      0 < L u₀ ∨ 0 < L v₀ := by
    by_contra hn
    have hu : L u₀ ≤ 0 := not_lt.mp (fun h => hn (Or.inl h))
    have hv : L v₀ ≤ 0 := not_lt.mp (fun h => hn (Or.inr h))
    obtain ⟨x, hxV, hxK, hxpos⟩ := _root_.mem_closure_iff.mp hcl V hV hzV
    have half (u : V3) (hu : L u ≤ 0) :
        convexHull ℝ ((insert u edge : Finset V3) : Set V3) ⊆ {x | L x ≤ 0} := by
      apply convexHull_min ?_ ((convex_Iic (0 : ℝ)).linear_preimage L.toLinearMap)
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hu
      · exact (heL x hx).le
    rcases (hgerm x hxV).mp hxK with hx | hx
    · have hle : L x ≤ 0 := half u₀ hu (hua.symm ▸ hx)
      exact (not_lt_of_ge hle) hxpos
    · have hle : L x ≤ 0 := half v₀ hv (hvb.symm ▸ hx)
      exact (not_lt_of_ge hle) hxpos
  have hpos := signed ell hezero hpositive
  have hneg : ell u₀ < 0 ∨ ell v₀ < 0 := by
    have hzeroNeg : ∀ x ∈ edge, (-ell) x = 0 := by
      intro x hx
      change -(c x).2 = 0
      rw [hezero x hx, neg_zero]
    have hnegcl : z ∈ closure (K.space ∩ {x | (-ell) x > 0}) := by
      simpa [ell, neg_pos] using hnegative
    have h := signed (-ell) hzeroNeg hnegcl
    simpa only [neg_apply, neg_pos] using h
  obtain ⟨a₁, b₁, u, v, ha₁, hb₁, hau, hbv, hu, hv, hgerm'⟩ :
      ∃ (a₁ b₁ : Finset V3) (u v : V3), a₁ ∈ K.faces ∧ b₁ ∈ K.faces ∧
        insert u edge = a₁ ∧ insert v edge = b₁ ∧ ell u < 0 ∧ 0 < ell v ∧
        ∀ x ∈ V, x ∈ K.space ↔
          x ∈ convexHull ℝ (a₁ : Set V3) ∪ convexHull ℝ (b₁ : Set V3) := by
    rcases hneg with hu | hv
    · exact ⟨a₀, b₀, u₀, v₀, ha₀.1, hb₀.1, hua, hvb, hu,
        hpos.resolve_left hu.not_gt, hgerm⟩
    · refine ⟨b₀, a₀, v₀, u₀, hb₀.1, ha₀.1, hvb, hua, hv,
        hpos.resolve_right hv.not_gt, ?_⟩
      intro x hx
      exact (hgerm x hx).trans or_comm
  have huK : u ∈ K.vertices := K.face_subset_vertices ha₁
    (hau ▸ Finset.mem_insert_self _ _)
  have hvK : v ∈ K.vertices := K.face_subset_vertices hb₁
    (hbv ▸ Finset.mem_insert_self _ _)
  have hunew : ell (H.map 1 u) < 0 := ((hsigns u (hKR huK) hu.ne 1).2).mpr hu
  have hvnew : 0 < ell (H.map 1 v) := ((hsigns v (hKR hvK) hv.ne' 1).1).mpr hv
  have huedge : u ∉ edge := fun h => hu.ne (hezero u h)
  have ha3 : a₁.card = 3 := by rw [← hau, Finset.card_insert_of_notMem huedge, he2]
  have hNa : a₁.image (H.map 1) ∈ N.faces :=
    (hHK.image_mem_embeddedImage_iff hHi (K.subset_space ha₁)).mpr ha₁
  have hNa3 : (a₁.image (H.map 1)).card = 3 := by
    rw [Finset.card_image_iff.mpr (H.map 1).injective.injOn, ha3]
  have hedgefix : edge.image (H.map 1) = edge := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
      exact ((hfix y (subset_convexHull ℝ _ hy)).symm.trans hyx) ▸ hy
    · intro hx
      exact Finset.mem_image.mpr ⟨x, hx, hfix x (subset_convexHull ℝ _ hx)⟩
  have hNahull : convexHull ℝ (a₁.image (H.map 1) : Set V3) =
      H.map 1 '' convexHull ℝ (a₁ : Set V3) := by
    rw [Finset.coe_image, ← hHK.image_convexHull ha₁]
  have hzNa : z ∈ convexHull ℝ (a₁.image (H.map 1) : Set V3) := by
    rw [hNahull]
    exact ⟨z, convexHull_mono (by rw [← hau]; exact Finset.subset_insert _ _)
      (intrinsicInterior_subset hzedge), hzfix⟩
  let plane := affineSpan ℝ (a₁.image (H.map 1) : Set V3)
  have hzplane : z ∈ plane := convexHull_subset_affineSpan (s :=
    (a₁.image (H.map 1) : Set V3)) hzNa
  have huplane : H.map 1 u ∈ plane := subset_affineSpan ℝ _
    (Finset.mem_image.mpr ⟨u, hau ▸ Finset.mem_insert_self _ _, rfl⟩)
  have hA : ∃ x ∈ plane, ∃ y ∈ plane, ell x ≠ ell y := by
    refine ⟨H.map 1 u, huplane, z, hzplane, ?_⟩
    intro heq
    apply (ne_of_lt hunew)
    exact heq.trans hz0
  obtain ⟨F, hFzero, hFell', hFplane⟩ := plane.exists_centered_height_plane_coordinates
    (by simp) (N.finrank_faceDirection_of_card hNa hNa3) ell.toLinearMap.toAffineMap
    hA hzplane
  have hFell (x : C3) : ell (F x) = x.1.1 := by
    have h := hFell' x
    change ell (F x) = ell z + x.1.1 at h
    simpa only [hz0, zero_add] using h
  let swap : C3 ≃ₗ[ℝ] C3 :=
    { toFun := fun x => ((x.1.1, x.2), x.1.2)
      invFun := fun x => ((x.1.1, x.2), x.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let A := F.symm.trans swap.toAffineEquiv.toContinuousAffineEquiv
  have hAzero : A z = 0 := by
    change swap (F.symm z) = 0
    rw [← hFzero, F.symm_apply_apply, map_zero]
  have hAz : (A z).2 = 0 := congrArg Prod.snd hAzero
  have hAell (x : V3) : (A x).1.1 = ell x := by
    change (F.symm x).1.1 = ell x
    simpa only [F.apply_symm_apply] using (hFell (F.symm x)).symm
  have hAedge (x : V3) (hx : x ∈ edge) : (A x).1 = 0 := by
    apply Prod.ext
    · exact (hAell x).trans (hezero x hx)
    · change (F.symm x).2 = 0
      apply (hFplane _).mp
      rw [F.apply_symm_apply]
      apply subset_affineSpan ℝ _
      rw [← hau, Finset.image_insert, hedgefix]
      exact Finset.mem_insert_of_mem hx
  obtain ⟨r₀, s₀, hrs, hepair⟩ := Finset.card_eq_two.mp he2
  have hr₀ : r₀ ∈ edge := hepair.symm ▸ Finset.mem_insert_self _ _
  have hs₀ : s₀ ∈ edge := hepair.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hAr : A r₀ = (0, (A r₀).2) := Prod.ext (hAedge r₀ hr₀) rfl
  have hAs : A s₀ = (0, (A s₀).2) := Prod.ext (hAedge s₀ hs₀) rfl
  obtain ⟨wt, hwt, hsum, hval⟩ := (K.indep heK).exists_positive_weights_of_mem_intrinsicInterior
    hzedge
  have hmap := Finset.map_affineCombination (s := edge) id wt hsum A.toAffineEquiv.toAffineMap
  simp only [Finset.affineCombination_eq_linear_combination _ _ _ hsum,
    id_eq, Function.comp_apply] at hmap
  rw [hval] at hmap
  change A z = ∑ x ∈ edge, wt x • A x at hmap
  have hbalance : wt r₀ * (A r₀).2 + wt s₀ * (A s₀).2 = 0 := by
    have h := congrArg Prod.snd hmap.symm
    rw [hepair, Finset.sum_pair hrs] at h
    change wt r₀ * (A r₀).2 + wt s₀ * (A s₀).2 = (A z).2 at h
    exact h.trans hAz
  have hwr := hwt r₀ hr₀
  have hws := hwt s₀ hs₀
  have hparameters : (A r₀).2 ≠ (A s₀).2 := fun h =>
    hrs (A.injective (hAr.trans ((congrArg (fun d : ℝ => ((0 : ℝ × ℝ), d)) h).trans hAs.symm)))
  have hrnonzero : (A r₀).2 ≠ 0 := by
    intro hr0
    have hs0 : (A s₀).2 = 0 := by
      have hprod : wt s₀ * (A s₀).2 = 0 := by simpa only [hr0, mul_zero, zero_add] using hbalance
      exact (mul_eq_zero.mp hprod).resolve_left hws.ne'
    exact hparameters (hr0.trans hs0.symm)
  obtain ⟨r₁, s₁, hr₁, hs₁, hAr₁, hAs₁, hepair'⟩ :
      ∃ r₁ s₁ : V3, (A r₁).2 < 0 ∧ 0 < (A s₁).2 ∧
        A r₁ = (0, (A r₁).2) ∧ A s₁ = (0, (A s₁).2) ∧ edge = {r₁, s₁} := by
    rcases lt_or_gt_of_ne hrnonzero with hr | hr
    · have hs : 0 < (A s₀).2 := by
        by_contra hn
        have h₁ := mul_neg_of_pos_of_neg hwr hr
        have h₂ := mul_nonpos_of_nonneg_of_nonpos hws.le (not_lt.mp hn)
        linarith
      exact ⟨r₀, s₀, hr, hs, hAr, hAs, hepair⟩
    · have hs : (A s₀).2 < 0 := by
        by_contra hn
        have h₁ := mul_pos hwr hr
        have h₂ := mul_nonneg hws.le (not_lt.mp hn)
        linarith
      exact ⟨s₀, r₀, hs, hr, hAs, hAr, hepair.trans (Finset.pair_comm _ _)⟩
  let u' := (A (H.map 1 u)).1
  let v' := (A (H.map 1 v)).1
  let hgt := ContinuousLinearMap.fst ℝ ℝ ℝ
  have hu' : hgt u' < 0 := by change (A (H.map 1 u)).1.1 < 0; rw [hAell]; exact hunew
  have hv' : 0 < hgt v' := by change 0 < (A (H.map 1 v)).1.1; rw [hAell]; exact hvnew
  have hu'0 : u' ≠ 0 := fun h => hu'.ne (by rw [h, map_zero])
  have hv'0 : v' ≠ 0 := fun h => hv'.ne' (by rw [h, map_zero])
  obtain ⟨Nu, hNu, h0Nu, htriU⟩ := exists_open_vertical_triangle_germ hu'0 hr₁ hs₁
    (A (H.map 1 u)).2
  obtain ⟨Nv, hNv, h0Nv, htriV⟩ := exists_open_vertical_triangle_germ hv'0 hr₁ hs₁
    (A (H.map 1 v)).2
  have hcoord (d : V3) (face : Finset V3) (hf : face ∈ K.faces)
      (hface : insert d edge = face) :
      A '' (H.map 1 '' convexHull ℝ (face : Set V3)) =
        convexHull ℝ ({(0, (A r₁).2), (0, (A s₁).2), A (H.map 1 d)} : Set C3) := by
    rw [hHK.image_convexHull hf]
    rw [← Finset.coe_image]
    change A.toAffineEquiv.toAffineMap ''
      convexHull ℝ (face.image (H.map 1) : Set V3) = _
    rw [A.toAffineEquiv.toAffineMap.image_convexHull]
    change convexHull ℝ (A '' (face.image (H.map 1) : Set V3)) = _
    rw [← hface, Finset.image_insert, hedgefix, hepair']
    simp only [Finset.coe_insert, Finset.coe_singleton]
    rw [Set.image_insert_eq, Set.image_pair, hAr₁, hAs₁]
    dsimp only
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  obtain ⟨axis, haxis, shear, hshear, hshear0, hheight, hnegativeRay, hpositiveRay⟩ :=
    hgt.exists_two_ray_straightening u' v' hu' hv'
  have hwholeRay (x : ℝ × ℝ) :
      ((∃ t : ℝ, 0 ≤ t ∧ x = t • u') ∨ (∃ t : ℝ, 0 ≤ t ∧ x = t • v')) ↔
        (shear x).2 - axis.2 * (shear x).1 = 0 := by
    have haxis₁ : axis.1 = 1 := haxis
    have hline (y : ℝ × ℝ) : (∃ t : ℝ, y = t • axis) ↔ y.2 - axis.2 * y.1 = 0 := by
      constructor
      · rintro ⟨t, rfl⟩
        change t * axis.2 - axis.2 * (t * axis.1) = 0
        rw [haxis₁]
        ring
      · intro h
        refine ⟨y.1, Prod.ext ?_ ?_⟩
        · change y.1 = y.1 * axis.1
          rw [haxis₁, mul_one]
        · change y.2 = y.1 * axis.2
          linarith
    rw [← hline]
    constructor
    · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · exact ⟨t * hgt u', hnegativeRay t ht⟩
      · exact ⟨t * hgt v', hpositiveRay t ht⟩
    · rintro ⟨t, ht⟩
      by_cases ht0 : 0 ≤ t
      · have hquot := div_nonneg ht0 hv'.le
        refine Or.inr ⟨t / hgt v', hquot, shear.injective ?_⟩
        rw [ht, hpositiveRay _ hquot, div_mul_cancel₀ _ hv'.ne']
      · have hquot := div_nonneg_of_nonpos (lt_of_not_ge ht0).le hu'.le
        refine Or.inl ⟨t / hgt u', hquot, shear.injective ?_⟩
        rw [ht, hnegativeRay _ hquot, div_mul_cancel₀ _ hu'.ne]
  let product := shear.prodCongr (Homeomorph.refl ℝ)
  have hproduct : product.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid C3 := by
    have hs : LocallyPiecewiseAffineOn shear univ ∧
        LocallyPiecewiseAffineOn shear.symm univ := hshear
    have hid : LocallyPiecewiseAffineOn (id : ℝ → ℝ) univ :=
      locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ ℝ) isOpen_univ
    constructor
    · change LocallyPiecewiseAffineOn (Prod.map shear id) univ
      simpa only [univ_prod_univ] using hs.1.prodMap hid
    · change LocallyPiecewiseAffineOn (Prod.map shear.symm id) univ
      simpa only [univ_prod_univ] using hs.2.prodMap hid
  let normalize : C3 ≃ₗ[ℝ] C3 :=
    { toFun := fun x => ((x.1.2 - axis.2 * x.1.1, x.2), x.1.1)
      invFun := fun x => ((x.2, x.1.1 + axis.2 * x.2), x.1.2)
      left_inv := by intro x; ext <;> dsimp <;> ring
      right_inv := by intro x; ext <;> dsimp <;> ring
      map_add' := by intro x y; ext <;> dsimp <;> ring
      map_smul' := by intro r x; ext <;> dsimp <;> ring }
  let B := normalize.toAffineEquiv.toContinuousAffineEquiv
  let Fglobal := (A.toHomeomorph.trans product).trans B.toHomeomorph
  have hglobal (x : V3) :
      Fglobal x = (( (shear (A x).1).2 - axis.2 * (shear (A x).1).1,
        (A x).2), (shear (A x).1).1) := rfl
  have hglobal0 : Fglobal z = 0 := by
    rw [hglobal, hAzero]
    change (((shear (0 : ℝ × ℝ)).2 - axis.2 * (shear 0).1, 0), (shear 0).1) = 0
    rw [hshear0]
    change ((0 - axis.2 * 0, (0 : ℝ)), (0 : ℝ)) = ((0, 0), 0)
    simp
  have hglobalHeight (x : V3) : (Fglobal x).2 = ell x :=
    (hheight (A x).1).trans (hAell x)
  have hglobalPL : LocallyPiecewiseAffineOn Fglobal univ := by
    have h := (locallyPiecewiseAffineOn_affine B.toContinuousAffineMap isOpen_univ).comp
      (hproduct.1.comp (locallyPiecewiseAffineOn_affine A.toContinuousAffineMap isOpen_univ))
    change LocallyPiecewiseAffineOn (B ∘ product ∘ A)
      ((univ ∩ A ⁻¹' univ) ∩ (product ∘ A) ⁻¹' univ) at h
    change LocallyPiecewiseAffineOn (B ∘ product ∘ A) univ
    simpa only [preimage_univ, inter_univ] using h
  let O := interior J.space ∩ (Q.target ∩ Q.symm ⁻¹' W)
  have hO : IsOpen O := isOpen_interior.inter (Q.symm.isOpen_inter_preimage hW)
  let Tsource := O ∩ ((H.map 1) '' V ∩ A ⁻¹' (Nu ∩ Nv))
  have hTsource : IsOpen Tsource := hO.inter
    (((H.map 1).isOpenMap _ hV).inter ((hNu.inter hNv).preimage A.continuous))
  have hzTsource : z ∈ Tsource :=
    ⟨⟨hzJ, hJQ (interior_subset hzJ), hzW⟩,
      ⟨z, hzV, hzfix⟩, by change A z ∈ Nu ∩ Nv; rw [hAzero]; exact ⟨h0Nu, h0Nv⟩⟩
  let localChart := Fglobal.toOpenPartialHomeomorphOfImageEq Tsource hTsource
    (Fglobal '' Tsource) rfl
  have hlocal (x : V3) (hx : x ∈ Tsource) :
      x ∈ N.space ↔ (localChart x).1.1 = 0 := by
    have hxn := hx.2.1
    obtain ⟨y, hyV, rfl⟩ := hxn
    have hmem : H.map 1 y ∈ N.space ↔ y ∈ K.space := by
      rw [hNs]
      exact (H.map 1).injective.mem_set_image
    rw [hmem, hgerm' y hyV]
    change _ ↔ (Fglobal (H.map 1 y)).1.1 = 0
    rw [hglobal]
    change y ∈ convexHull ℝ (a₁ : Set V3) ∪ convexHull ℝ (b₁ : Set V3) ↔
      (shear (A (H.map 1 y)).1).2 - axis.2 * (shear (A (H.map 1 y)).1).1 = 0
    have htriangle (face : Finset V3) :
        A (H.map 1 y) ∈ A '' (H.map 1 '' convexHull ℝ (face : Set V3)) ↔
          y ∈ convexHull ℝ (face : Set V3) := by
      rw [A.injective.mem_set_image, (H.map 1).injective.mem_set_image]
    rw [Set.mem_union, ← htriangle a₁, ← htriangle b₁,
      hcoord u a₁ ha₁ hau, hcoord v b₁ hb₁ hbv]
    have hucoord : A (H.map 1 u) = (u', (A (H.map 1 u)).2) := rfl
    have hvcoord : A (H.map 1 v) = (v', (A (H.map 1 v)).2) := rfl
    rw [hucoord, hvcoord, htriU _ hx.2.2.1, htriV _ hx.2.2.2]
    exact hwholeRay (A (H.map 1 y)).1
  let T := Q.trans (localChart.trans c.symm.toHomeomorph.toOpenPartialHomeomorph)
  have hzT : Q.symm z ∈ T.source := by
    refine ⟨Q.map_target (hJQ (interior_subset hzJ)), ?_, mem_univ _⟩
    change Q (Q.symm z) ∈ Tsource
    rw [Q.right_inv (hJQ (interior_subset hzJ))]
    exact hzTsource
  have hvalue (y : s.Carrier) : c (T y) = localChart (Q y) := c.apply_symm_apply _
  have hsource (y : s.Carrier) (hy : y ∈ T.source) :
      y ∈ W ∩ (Q.source ∩ interior (s.projection ⁻¹' R)) := by
    have hinside : Q y ∈ O := hy.2.1.1
    have hyW : y ∈ W := by
      have h := hinside.2.2
      change Q.symm (Q y) ∈ W at h
      rwa [Q.left_inv hy.1] at h
    exact ⟨hyW, hy.1, (hQU hy.1).2⟩
  refine ⟨T, hzT, ?_, hsource, ?_, ?_, ?_, ?_⟩
  · change c.symm (Fglobal (Q (Q.symm z))) = 0
    rw [Q.right_inv (hJQ (interior_subset hzJ)), hglobal0, map_zero]
  · intro k
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    have hf := (locallyPiecewiseAffineOn_affine
      c.symm.toContinuousLinearMap.toContinuousAffineMap isOpen_univ).comp
      (hglobalPL.mono localChart.open_source (subset_univ _))
    exact (hf.comp (hQPL k).1).mono ((s.charts k).symm.trans T).open_source
      (fun x hx => ⟨⟨hx.1, hx.2.1⟩, hx.2.2.1, mem_univ _⟩)
  · ext x
    constructor
    · intro hx
      rcases w.whole_preimage.subset (hQw (hsource _ hx).2.1) with hl | hr
      · exact Or.inl ⟨hl, hx⟩
      · exact Or.inr ⟨hr, hx⟩
    · exact fun h => h.elim And.right And.right
  · intro y hy
    rw [hleft y hy.1, hvalue]
    change ell (Q y) = 0 ↔ (Fglobal (Q y)).2 = 0
    rw [hglobalHeight]
  · intro y hy
    have hyJ : Q y ∈ J.space := interior_subset hy.2.1.1.1
    have hright : y ∈ p '' (new.map '' D ∩ w.right.source) ↔ Q y ∈ N.space := by
      rw [hNs, hKs, ← hnewimage]
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
    exact hlocal (Q y) hy.2.1


theorem OriginalGeneralPositionData.exists_protected_edge_crossed_charts
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
            J.faces.Finite ∧ J.space ⊆ Q.target ∧
            (0 : V3) ∈ interior J.space ∧ 0 < ρ ∧ ball (0 : V3) ρ ⊆ interior J.space ∧
            P.space = (w.right.trans Q) ''
              (data.initial.map '' D ∩ (w.right.trans Q).source) ∩ J.space ∧
            P₀.space = P.space \ ball (0 : V3) ρ ∧ K.faces.Finite ∧ K.space = P.space ∧
            R₀.faces.Finite ∧ R₀.IsSubdivision J ∧ K ≤ R₀ ∧
            K.AffineOnFaces q ∧ InjOn q K.space ∧ K₀ ≤ K ∧ K₀.space = P₀.space ∧
            (∀ z ∈ K.space, z ∈ interior J.space → q z ∈ interior (q '' K.space)) ∧
            (step.projection ∘ step.inclusion) ⁻¹' (Q.symm '' J.space) =
              (w.left.trans Q).symm '' J.space ∪ (w.right.trans Q).symm '' J.space ∧
            L.faces.Finite ∧ L.space = J.space ∩ {z | (c z).2 = 0} ∧
            0 < δ ∧ (∀ v ∈ R₀.vertices, (c v).2 ≠ 0 → δ ≤ |(c v).2|) ∧
            (∀ v ∈ P₀.space, v ∈ interior J.space → (c v).2 = 0 →
              ∃ T : OpenPartialHomeomorph V3 C3,
                (0 : V3) ∈ T.source ∧ T 0 = 0 ∧
                LocallyPiecewiseAffineOn T.symm T.target ∧
                (∀ z ∈ T.source, z ∈ (fun x : V3 => -v + x) '' K.space ↔
                  (T z).1.1 = 0) ∧
                ∀ z ∈ T.source, (c z).2 = 0 ↔ (T z).2 = 0) ∧
            (∀ z ∈ P₀.space, z ∈ interior J.space → (c z).2 = 0 →
              z ∈ closure (K.space ∩ {x | 0 < (c x).2}) ∧
              z ∈ closure (K.space ∩ {x | (c x).2 < 0})) ∧
            ∀ ε : ℝ, 0 < ε → ∃ H : PLCarrierMotion J.space P₀.space ε,
              K.AffineOnFaces (H.map 1) ∧
              (∀ v ∈ K.vertices, (c v).2 ≠ 0 → ∀ u,
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
                (∀ y ∈ Q.source,
                  y ∈ (step.projection ∘ step.inclusion) ''
                    (new.map '' D ∩ w.left.source) ↔ (c (Q y)).2 = 0) ∧
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
                (∀ edge ∈ K₀.faces, edge.card = 2 → (∀ v ∈ edge, (c v).2 = 0) →
                  ∀ z ∈ intrinsicInterior ℝ (convexHull ℝ (edge : Set V3)),
                    z ∈ interior J.space → ∀ W : Set s.Carrier,
                      IsOpen W → Q.symm z ∈ W → ∃ T : OpenPartialHomeomorph s.Carrier V3,
                        Q.symm z ∈ T.source ∧ T (Q.symm z) = 0 ∧
                        T.source ⊆ W ∩ (Q.source ∩ interior (s.projection ⁻¹' R)) ∧
                        (∀ k, (s.charts k).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
                        (step.projection ∘ step.inclusion) ⁻¹' T.source =
                          (w.left.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∪
                            (w.right.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∧
                        (∀ y ∈ T.source,
                          y ∈ (step.projection ∘ step.inclusion) ''
                            (new.map '' D ∩ w.left.source) ↔ (c (T y)).2 = 0) ∧
                        ∀ y ∈ T.source,
                          y ∈ (step.projection ∘ step.inclusion) ''
                            (new.map '' D ∩ w.right.source) ↔ (c (T y)).1.1 = 0) ∧
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
    data.exists_protected_edge_crossed_charts_with_closed_support he hF hopen
      a b hab haint hpair U hU haU
  refine ⟨w, c, Q, J, P, P₀, R₀, K, K₀, L, q, ρ, δ, ?_⟩
  rcases h with ⟨ha, hb, haQ, hQzero, hQU, hQw, hQPL, hbranches,
    hJ, hJQ, hzeroJ, hρ, hball, _hclosed, hrest⟩
  exact ⟨ha, hb, haQ, hQzero, hQU, hQw, hQPL, hbranches,
    hJ, hJQ, hzeroJ, hρ, hball, hrest⟩


set_option maxHeartbeats 1600000 in






theorem Step.exists_original_protected_edge_crossed_charts
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    (old : StageMarkedDisk t R Fmark base Jgroup) :
    ∃ (initial : StageMarkedDisk t R Fmark base Jgroup)
      (eta : old.rim.Homotopy initial.rim),
      initial.basepath = old.basepath.trans (eta.evalAt squareRimBase) ∧
      ∀ a b : D, a ≠ b → (a : V2) ∉ Rim →
        step.projection (step.inclusion (initial.map a)) =
          step.projection (step.inclusion (initial.map b)) →
        ∀ U : Set s.Carrier, IsOpen U →
          step.projection (step.inclusion (initial.map a)) ∈ U →
          ∃ (w : TwoBranchWindow (step.projection ∘ step.inclusion))
            (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3)
            (J P P₀ R₀ K K₀ L : SimplicialComplex ℝ V3)
            (q : V3 → ℝ × ℝ) (ρ δ : ℝ),
            initial.map a ∈ w.left.source ∧ initial.map b ∈ w.right.source ∧
            step.projection (step.inclusion (initial.map a)) ∈ Q.source ∧
            Q (step.projection (step.inclusion (initial.map a))) = 0 ∧
            Q.source ⊆ U ∩ interior (s.projection ⁻¹' R) ∧ Q.source ⊆ w.target ∧
            (∀ k, (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
            (∀ k, (t.charts k).symm.trans (w.left.trans Q) ∈ piecewiseAffineGroupoid V3 ∧
              (t.charts k).symm.trans (w.right.trans Q) ∈ piecewiseAffineGroupoid V3) ∧
            J.faces.Finite ∧ J.space ⊆ Q.target ∧
            (0 : V3) ∈ interior J.space ∧ 0 < ρ ∧ ball (0 : V3) ρ ⊆ interior J.space ∧
            P.space = (w.right.trans Q) ''
              (initial.map '' D ∩ (w.right.trans Q).source) ∩ J.space ∧
            P₀.space = P.space \ ball (0 : V3) ρ ∧ K.faces.Finite ∧ K.space = P.space ∧
            R₀.faces.Finite ∧ R₀.IsSubdivision J ∧ K ≤ R₀ ∧
            K.AffineOnFaces q ∧ InjOn q K.space ∧ K₀ ≤ K ∧ K₀.space = P₀.space ∧
            (∀ z ∈ K.space, z ∈ interior J.space → q z ∈ interior (q '' K.space)) ∧
            (step.projection ∘ step.inclusion) ⁻¹' (Q.symm '' J.space) =
              (w.left.trans Q).symm '' J.space ∪ (w.right.trans Q).symm '' J.space ∧
            L.faces.Finite ∧ L.space = J.space ∩ {z | (c z).2 = 0} ∧
            0 < δ ∧ (∀ v ∈ R₀.vertices, (c v).2 ≠ 0 → δ ≤ |(c v).2|) ∧
            (∀ v ∈ P₀.space, v ∈ interior J.space → (c v).2 = 0 →
              ∃ T : OpenPartialHomeomorph V3 C3,
                (0 : V3) ∈ T.source ∧ T 0 = 0 ∧
                LocallyPiecewiseAffineOn T.symm T.target ∧
                (∀ z ∈ T.source, z ∈ (fun x : V3 => -v + x) '' K.space ↔
                  (T z).1.1 = 0) ∧
                ∀ z ∈ T.source, (c z).2 = 0 ↔ (T z).2 = 0) ∧
            (∀ z ∈ P₀.space, z ∈ interior J.space → (c z).2 = 0 →
              z ∈ closure (K.space ∩ {x | 0 < (c x).2}) ∧
              z ∈ closure (K.space ∩ {x | (c x).2 < 0})) ∧
            ∀ ε : ℝ, 0 < ε → ∃ H : PLCarrierMotion J.space P₀.space ε,
              K.AffineOnFaces (H.map 1) ∧
              (∀ v ∈ K.vertices, (c v).2 ≠ 0 → ∀ u,
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
                (∀ x, new.map x = G 1 (initial.map x)) ∧ new.rim = initial.rim ∧
                HEq new.basepath initial.basepath ∧
                (∀ x : Rim, new.map x = initial.map x) ∧
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
                (∀ edge ∈ K₀.faces, edge.card = 2 → (∀ v ∈ edge, (c v).2 = 0) →
                  ∀ z ∈ intrinsicInterior ℝ (convexHull ℝ (edge : Set V3)),
                    z ∈ interior J.space → ∀ W : Set s.Carrier,
                      IsOpen W → Q.symm z ∈ W → ∃ T : OpenPartialHomeomorph s.Carrier V3,
                        Q.symm z ∈ T.source ∧ T (Q.symm z) = 0 ∧
                        T.source ⊆ W ∩ (Q.source ∩ interior (s.projection ⁻¹' R)) ∧
                        (∀ k, (s.charts k).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
                        (step.projection ∘ step.inclusion) ⁻¹' T.source =
                          (w.left.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∪
                            (w.right.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∧
                        (∀ y ∈ T.source,
                          y ∈ (step.projection ∘ step.inclusion) ''
                            (new.map '' D ∩ w.left.source) ↔ (c (T y)).2 = 0) ∧
                        ∀ y ∈ T.source,
                          y ∈ (step.projection ∘ step.inclusion) ''
                            (new.map '' D ∩ w.right.source) ↔ (c (T y)).1.1 = 0) ∧
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
  let data := step.originalGeneralPositionData he hF hopen old
  refine ⟨data.initial, data.eta, data.basepath, ?_⟩
  intro a b hab haint hpair U hU haU
  obtain ⟨w, c, Q, J, P, P₀, R₀, K, K₀, L, q, ρ, δ,
    ha, hb, haQ, hQzero, hQU, hQw, hQPL, hbranches, hJ, hJQ, hzeroJ,
    hρ, hball, hPs, hP₀s, hK, hKs, hR₀, hR₀J, hKR, hqK, hqi, hK₀K,
    hK₀s, hparam, hwhole, hL, hLs, hδ, hmargin, holdcharts,
    happroach, hmotions⟩ :=
    data.exists_protected_edge_crossed_charts he hF hopen a b hab haint hpair U hU haU
  refine ⟨w, c, Q, J, P, P₀, R₀, K, K₀, L, q, ρ, δ,
    ha, hb, haQ, hQzero, hQU, hQw, hQPL, hbranches, hJ, hJQ, hzeroJ,
    hρ, hball, hPs, hP₀s, hK, hKs, hR₀, hR₀J, hKR, hqK, hqi, hK₀K,
    hK₀s, hparam, hwhole, hL, hLs, hδ, hmargin, holdcharts, happroach, ?_⟩
  intro ε hε
  obtain ⟨H, hHK, hsigns, hzeroVertices, hfaces, hposition,
    Kamb, Knew, hKamb, hKambs, hKN, hKnews, hK₀N, hqnew, hqin,
    hincidence, hnewlinks, G, new, hG, hGinv, hGzero, hformula,
    hGout, hGprotected, hGleft, hGfront, hGregion, hGPL, hnewmap,
    hrim, hnewpath, hrimpoint, hnewimage, _hleft, hvertexcharts, hedgecharts, relation⟩ :=
    hmotions ε hε
  exact ⟨H, hHK, hsigns, hzeroVertices, hfaces, hposition,
    Kamb, Knew, hKamb, hKambs, hKN, hKnews, hK₀N, hqnew, hqin,
    hincidence, hnewlinks, G, new, hG, hGinv, hGzero, hformula,
    hGout, hGprotected, hGleft, hGfront, hGregion, hGPL, hnewmap,
    hrim, hnewpath, hrimpoint, hnewimage, hvertexcharts, hedgecharts, relation⟩

end Geometry.OriginalPLTower
