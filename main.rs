use rand::Rng;
use std::collections::HashMap;

// Protocol parameters (REDUCED FOR PERFORMANCE)
const LAMBDA: usize = 32;  // Total bit length (reduced from 128)
const BLOCK_SIZE: usize = 8;  // ℓ - size of each block (reduced from 16)
const EPSILON: usize = 2;  // Threshold distance per block (reduced from 3)
const NUM_BLOCKS: usize = LAMBDA / BLOCK_SIZE;  // B = λ/ℓ = 4

// NOTE: Original parameters cause polynomial explosion
// LAMBDA=128, BLOCK_SIZE=16, EPSILON=3 → 14 multiplications per block
// This creates millions of polynomial terms and hangs
// Reduced parameters: LAMBDA=32, BLOCK_SIZE=8, EPSILON=2 → 7 multiplications

// Field prime (large prime for finite field F_p)
const FIELD_PRIME: i128 = 2147483647; // 2^31 - 1 (Mersenne prime)

/// Modular arithmetic helpers
fn mod_add(a: i128, b: i128, m: i128) -> i128 {
    ((a % m + b % m) % m + m) % m
}

fn mod_mul(a: i128, b: i128, m: i128) -> i128 {
    ((a % m) * (b % m) % m + m) % m
}

fn mod_pow(mut base: i128, mut exp: usize, m: i128) -> i128 {
    base = (base % m + m) % m;
    let mut result = 1i128;
    while exp > 0 {
        if exp % 2 == 1 {
            result = mod_mul(result, base, m);
        }
        base = mod_mul(base, base, m);
        exp /= 2;
    }
    result
}

/// Represents a monomial
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Monomial {
    powers: Vec<(usize, usize)>,
}

impl Monomial {
    fn new() -> Self {
        Monomial { powers: Vec::new() }
    }
    
    fn constant() -> Self {
        Monomial::new()
    }
    
    fn with_var(mut self, var_idx: usize, power: usize) -> Self {
        if power > 0 {
            if let Some(pos) = self.powers.iter().position(|(idx, _)| *idx == var_idx) {
                self.powers[pos].1 += power;
            } else {
                self.powers.push((var_idx, power));
                self.powers.sort_by_key(|(idx, _)| *idx);
            }
        }
        self
    }
    
    fn evaluate(&self, vars: &[i128]) -> i128 {
        let mut result = 1i128;
        for &(var_idx, power) in &self.powers {
            if var_idx < vars.len() {
                result = mod_mul(result, mod_pow(vars[var_idx], power, FIELD_PRIME), FIELD_PRIME);
            }
        }
        result
    }
    
    fn multiply(&self, other: &Monomial) -> Monomial {
        let mut result = Monomial::new();
        let mut i = 0;
        let mut j = 0;
        
        while i < self.powers.len() || j < other.powers.len() {
            if i >= self.powers.len() {
                result.powers.push(other.powers[j]);
                j += 1;
            } else if j >= other.powers.len() {
                result.powers.push(self.powers[i]);
                i += 1;
            } else if self.powers[i].0 < other.powers[j].0 {
                result.powers.push(self.powers[i]);
                i += 1;
            } else if self.powers[i].0 > other.powers[j].0 {
                result.powers.push(other.powers[j]);
                j += 1;
            } else {
                let var_idx = self.powers[i].0;
                let total_power = self.powers[i].1 + other.powers[j].1;
                result.powers.push((var_idx, total_power));
                i += 1;
                j += 1;
            }
        }
        result
    }
}

/// Multivariate polynomial with modular arithmetic
#[derive(Debug, Clone)]
struct MultivariatePolynomial {
    terms: HashMap<Monomial, i128>,
}

impl MultivariatePolynomial {
    fn new() -> Self {
        MultivariatePolynomial { terms: HashMap::new() }
    }
    
    fn constant(c: i128) -> Self {
        let mut poly = MultivariatePolynomial::new();
        poly.terms.insert(Monomial::constant(), mod_add(c, 0, FIELD_PRIME));
        poly
    }
    
    fn add_term(&mut self, monomial: Monomial, coefficient: i128) {
        let entry = self.terms.entry(monomial).or_insert(0);
        *entry = mod_add(*entry, coefficient, FIELD_PRIME);
    }
    
    fn evaluate(&self, vars: &[i128]) -> i128 {
        let mut result = 0i128;
        for (monomial, &coeff) in &self.terms {
            let term_value = mod_mul(coeff, monomial.evaluate(vars), FIELD_PRIME);
            result = mod_add(result, term_value, FIELD_PRIME);
        }
        result
    }
    
    fn subtract(&self, other: &MultivariatePolynomial) -> MultivariatePolynomial {
        let mut result = self.clone();
        for (monomial, &coeff) in &other.terms {
            result.add_term(monomial.clone(), -coeff);
        }
        result.terms.retain(|_, &mut coeff| coeff != 0);
        result
    }
    
    fn multiply(&self, other: &MultivariatePolynomial) -> MultivariatePolynomial {
        let mut result = MultivariatePolynomial::new();
        for (m1, &c1) in &self.terms {
            for (m2, &c2) in &other.terms {
                let new_monomial = m1.multiply(m2);
                let new_coeff = mod_mul(c1, c2, FIELD_PRIME);
                result.add_term(new_monomial, new_coeff);
            }
        }
        result.terms.retain(|_, &mut coeff| coeff != 0);
        result
    }
    
    fn add_inplace(&mut self, other: &MultivariatePolynomial) {
        for (monomial, &coeff) in &other.terms {
            self.add_term(monomial.clone(), coeff);
        }
        self.terms.retain(|_, &mut coeff| coeff != 0);
    }
    
    fn degree(&self) -> usize {
        self.terms.keys().map(|m| {
            m.powers.iter().map(|(_, power)| power).sum::<usize>()
        }).max().unwrap_or(0)
    }
    
    fn num_terms(&self) -> usize {
        self.terms.len()
    }
}

#[derive(Debug, Clone)]
struct Block {
    bits: Vec<u8>,
}

impl Block {
    fn new(bits: Vec<u8>) -> Self {
        assert_eq!(bits.len(), BLOCK_SIZE);
        assert!(bits.iter().all(|&b| b == 0 || b == 1));
        Block { bits }
    }
    
    fn to_field_elements(&self) -> Vec<i128> {
        self.bits.iter().map(|&b| b as i128).collect()
    }
    
    fn hamming_distance(&self, other: &Block) -> usize {
        self.bits.iter().zip(other.bits.iter())
            .map(|(&a, &b)| if a != b { 1 } else { 0 })
            .sum()
    }
}

#[derive(Debug, Clone)]
struct BinaryVector {
    blocks: Vec<Block>,
}

impl BinaryVector {
    fn new(bits: Vec<u8>) -> Self {
        assert_eq!(bits.len(), LAMBDA);
        assert!(bits.iter().all(|&b| b == 0 || b == 1));
        
        let blocks: Vec<Block> = bits.chunks(BLOCK_SIZE)
            .map(|chunk| Block::new(chunk.to_vec()))
            .collect();
        
        BinaryVector { blocks }
    }
    
    fn random() -> Self {
        let mut rng = rand::thread_rng();
        let bits: Vec<u8> = (0..LAMBDA).map(|_| rng.gen_range(0..2)).collect();
        BinaryVector::new(bits)
    }
    
    fn get_block(&self, block_idx: usize) -> &Block {
        &self.blocks[block_idx]
    }
    
    fn to_bits(&self) -> Vec<u8> {
        self.blocks.iter().flat_map(|b| b.bits.clone()).collect()
    }
}

type DatabaseEntry = BinaryVector;

struct Database {
    entries: Vec<DatabaseEntry>,
}

impl Database {
    fn new(entries: Vec<DatabaseEntry>) -> Self {
        Database { entries }
    }
    
    fn random(n: usize) -> Self {
        let entries: Vec<DatabaseEntry> = (0..n)
            .map(|_| BinaryVector::random())
            .collect();
        Database { entries }
    }
}

/// TTP Protocol - Per-Entry Polynomials (Updated Version)
struct TTPProtocol {
    database: Database,
    /// Blinding values r_i for each database entry
    r_blinds: Vec<i128>,
    /// Per-entry polynomials S_i (one polynomial per database entry)
    entry_polynomials: Vec<MultivariatePolynomial>,
}

impl TTPProtocol {
    fn new(database: Database) -> Self {
        let n = database.entries.len();
        let mut rng = rand::thread_rng();
        
        // Generate blinding values r_i ∈ F_p for each database entry
        let r_blinds: Vec<i128> = (0..n)
            .map(|_| rng.gen_range(1..FIELD_PRIME))
            .collect();
        
        TTPProtocol {
            database,
            r_blinds,
            entry_polynomials: Vec::new(),
        }
    }
    
    /// Compute distance polynomial D_{i,b}(d^(b)) for entry i, block b
    /// D_{i,b} = Σ_{j=1}^{ℓ} (d^(b)[j] + d_i^(b)[j] - 2·d^(b)[j]·d_i^(b)[j])
    fn distance_polynomial_for_block(block_i: &Block, block_offset: usize) -> MultivariatePolynomial {
        let mut poly = MultivariatePolynomial::new();
        
        for j in 0..BLOCK_SIZE {
            let di_j = block_i.bits[j] as i128;
            let global_var_idx = block_offset * BLOCK_SIZE + j;
            
            // Constant term: d_i[j]
            if di_j != 0 {
                poly.add_term(Monomial::constant(), di_j);
            }
            
            // Linear term: d[j] * (1 - 2*d_i[j])
            let linear_coeff = 1 - 2 * di_j;
            if linear_coeff != 0 {
                poly.add_term(Monomial::new().with_var(global_var_idx, 1), linear_coeff);
            }
        }
        
        poly
    }
    
    /// Compute threshold polynomial Z_{i,b}(d^(b)) = ∏_{t=ε}^{ℓ} (D_{i,b}(d^(b)) - t)
    /// Z_{i,b} = 0 if D_{i,b} ≥ ε (NOT a match at block b)
    /// Z_{i,b} ≠ 0 if D_{i,b} < ε (IS a match at block b)
    fn threshold_polynomial_for_block(distance_poly: &MultivariatePolynomial) -> MultivariatePolynomial {
        let mut result = MultivariatePolynomial::constant(1);
        
        let num_factors = BLOCK_SIZE - EPSILON + 1;
        print!("      Computing product of {} factors...", num_factors);
        
        // Product from t = ε to ℓ
        for (idx, t) in (EPSILON..=BLOCK_SIZE).enumerate() {
            let constant_t = MultivariatePolynomial::constant(t as i128);
            let factor = distance_poly.subtract(&constant_t);
            result = result.multiply(&factor);
            
            if (idx + 1) % 3 == 0 || idx == num_factors - 1 {
                print!(" {}/{}", idx + 1, num_factors);
            }
        }
        println!(" done ({} terms)", result.num_terms());
        
        result
    }
    
    /// Build per-entry polynomials
    /// S_i(d) = Σ_{b=1}^{B} Z_{i,b}(d^(b)) + r_i
    fn build_entry_polynomials(&mut self) {
        println!("Building TTP per-entry polynomials...");
        println!("{}", "=".repeat(80));
        println!("Blinding values r_i: {:?}", &self.r_blinds);
        println!();
        
        self.entry_polynomials.clear();
        
        for (entry_idx, entry) in self.database.entries.iter().enumerate() {
            println!("Processing entry {}...", entry_idx);
            
            let mut s_i = MultivariatePolynomial::new();
            
            // Sum over all blocks for this entry
            for block_idx in 0..NUM_BLOCKS {
                let block = entry.get_block(block_idx);
                
                // Compute D_{i,b}
                let d_poly = Self::distance_polynomial_for_block(block, block_idx);
                
                // Compute Z_{i,b}
                let z_poly = Self::threshold_polynomial_for_block(&d_poly);
                
                // Add Z_{i,b} to S_i
                s_i.add_inplace(&z_poly);
            }
            
            // Add blinding r_i
            s_i.add_term(Monomial::constant(), self.r_blinds[entry_idx]);
            
            println!("  S_{}(d): {} terms, degree {}", 
                     entry_idx, s_i.num_terms(), s_i.degree());
            
            self.entry_polynomials.push(s_i);
        }
        
        println!("\nAll entry polynomials constructed!");
        println!("Total: {} entry polynomials (one per database entry)", self.entry_polynomials.len());
    }
    
    /// Client: Evaluate all S_i polynomials
    /// Returns [res_i]_n where res_i = S_i(d)
    fn client_evaluate(&self, client_query: &BinaryVector) -> Vec<i128> {
        assert_eq!(self.entry_polynomials.len(), self.database.entries.len(),
                   "Entry polynomials not built");
        
        let query_vars = client_query.to_bits().iter().map(|&b| b as i128).collect::<Vec<_>>();
        
        self.entry_polynomials.iter()
            .map(|s_i| s_i.evaluate(&query_vars))
            .collect()
    }
    
    /// Server: Unmask and check results
    /// Returns true if ANY entry matches (at least one res_i ≠ 1 after unmasking)
    fn server_check(&self, res_values: &[i128]) -> (bool, Vec<usize>) {
        assert_eq!(res_values.len(), self.r_blinds.len());
        
        let mut matching_entries = Vec::new();
        
        for (i, &res_i) in res_values.iter().enumerate() {
            // Unmask: compute res_i - r_i
            let unmasked = mod_add(res_i, -self.r_blinds[i], FIELD_PRIME);
            
            // If unmasked ≠ 0: this entry matches
            if unmasked != 0 {
                matching_entries.push(i);
            }
        }
        
        let has_match = !matching_entries.is_empty();
        (has_match, matching_entries)
    }
    
    /// Verification: check if entry actually matches
    fn entry_matches(&self, entry_idx: usize, client_query: &BinaryVector) -> bool {
        let entry = &self.database.entries[entry_idx];
        (0..NUM_BLOCKS).all(|b| {
            client_query.get_block(b).hamming_distance(entry.get_block(b)) < EPSILON
        })
    }
    
    /// Get all actual matching entries (for verification)
    fn get_actual_matches(&self, client_query: &BinaryVector) -> Vec<usize> {
        (0..self.database.entries.len())
            .filter(|&i| self.entry_matches(i, client_query))
            .collect()
    }
    
    fn total_hamming_distance(d: &BinaryVector, d_i: &BinaryVector) -> usize {
        (0..NUM_BLOCKS)
            .map(|b| d.get_block(b).hamming_distance(d_i.get_block(b)))
            .sum()
    }
}

fn format_binary_vector(v: &BinaryVector) -> String {
    let bits = v.to_bits();
    let blocks: Vec<String> = bits.chunks(BLOCK_SIZE)
        .map(|chunk| {
            chunk.iter()
                .map(|&b| if b == 1 { '1' } else { '0' })
                .collect::<String>()
        })
        .collect();
    blocks.join(" ")
}

fn main() {
    println!("TTP Threshold Protocol - Per-Entry Polynomials (Final Version)");
    println!("===============================================================");
    println!("λ (LAMBDA) = {} (reduced from 128 for performance)", LAMBDA);
    println!("ℓ (BLOCK_SIZE) = {} (reduced from 16 for performance)", BLOCK_SIZE);
    println!("ε (EPSILON) = {} (reduced from 3 for performance)", EPSILON);
    println!("B (NUM_BLOCKS) = {}", NUM_BLOCKS);
    println!("Field Prime p = {}", FIELD_PRIME);
    println!();
    println!("NOTE: Original parameters (λ=128, ℓ=16, ε=3) cause polynomial explosion:");
    println!("      Each Z_{{i,b}} requires 14 polynomial multiplications,");
    println!("      creating millions of terms. Reduced parameters for demonstration.");
    println!();
    
    println!("PROTOCOL STRUCTURE:");
    println!("{}", "=".repeat(80));
    println!("• One polynomial S_i per database entry (n polynomials total)");
    println!("• S_i(d) = Σ_{{b=1}}^B Z_{{i,b}}(d^(b)) + r_i");
    println!("• Z_{{i,b}} = 0 if block b of entry i doesn't match (distance ≥ ε)");
    println!("• Z_{{i,b}} ≠ 0 if block b of entry i matches (distance < ε)");
    println!("• Client computes res_i = S_i(d) for all i ∈ [n]");
    println!("• Server unmasks: res_i - r_i");
    println!("• If (res_i - r_i) ≠ 0: entry i fully matches (all blocks match)");
    println!("• If (res_i - r_i) = 0: entry i doesn't fully match\n");
    
    let db = Database::random(5);  // Reduced from 10 for performance
    
    println!("DATABASE ENTRIES:");
    println!("{}", "=".repeat(80));
    for (i, entry) in db.entries.iter().enumerate() {
        println!("Entry {}: {}", i, format_binary_vector(entry));
    }
    println!();
    
    let client_query = BinaryVector::random();
    
    println!("CLIENT QUERY:");
    println!("{}", "=".repeat(80));
    println!("Query:   {}", format_binary_vector(&client_query));
    println!();
    
    let mut protocol = TTPProtocol::new(db);
    protocol.build_entry_polynomials();
    println!();
    
    println!("CLIENT COMPUTATION:");
    println!("{}", "=".repeat(80));
    let res_values = protocol.client_evaluate(&client_query);
    println!("Computed {} results [res_i]_n:", res_values.len());
    for (i, &res) in res_values.iter().enumerate() {
        println!("  res_{} = S_{}(d) = {} (mod {})", i, i, res, FIELD_PRIME);
    }
    println!();
    
    println!("SERVER VERIFICATION:");
    println!("{}", "=".repeat(80));
    let (has_match, detected_matches) = protocol.server_check(&res_values);
    
    for (i, &res) in res_values.iter().enumerate() {
        let unmasked = mod_add(res, -protocol.r_blinds[i], FIELD_PRIME);
        println!("Entry {}: res_{} - r_{} = {} {}", 
                 i, i, i, unmasked,
                 if unmasked != 0 { "✓ MATCH" } else { "✗" });
    }
    println!();
    
    if has_match {
        println!("✓ SERVER RESULT: MATCH EXISTS");
        println!("  Detected matching entries: {:?}", detected_matches);
    } else {
        println!("✗ SERVER RESULT: NO MATCH");
    }
    println!();
    
    println!("VERIFICATION (Ground Truth):");
    println!("{}", "=".repeat(80));
    let actual_matches = protocol.get_actual_matches(&client_query);
    
    if !actual_matches.is_empty() {
        println!("Actual matching entries: {:?}", actual_matches);
        for idx in &actual_matches {
            let distance = TTPProtocol::total_hamming_distance(
                &client_query,
                &protocol.database.entries[*idx]
            );
            println!("  Entry {}: total distance = {}", idx, distance);
        }
    } else {
        println!("No actual matches");
    }
    
    println!();
    let correct = detected_matches == actual_matches;
    println!("Protocol correctness: {}", if correct { "✓ CORRECT" } else { "✗ INCORRECT" });
    
    println!();
    println!("DETAILED ANALYSIS:");
    println!("{}", "=".repeat(80));
    for (i, entry) in protocol.database.entries.iter().enumerate() {
        let total_distance = TTPProtocol::total_hamming_distance(&client_query, entry);
        
        print!("Entry {}: distance = {:3} | Blocks: [", i, total_distance);
        for b in 0..NUM_BLOCKS {
            let block_dist = client_query.get_block(b).hamming_distance(entry.get_block(b));
            let is_match = block_dist < EPSILON;
            print!("{:2}{}", block_dist, if is_match { "✓" } else { "✗" });
            if b < NUM_BLOCKS - 1 { print!(" "); }
        }
        
        let fully_matches = protocol.entry_matches(i, &client_query);
        println!("] {}", if fully_matches { "✓ FULL MATCH" } else { "" });
    }
    
    println!();
    println!("SECURITY & EFFICIENCY:");
    println!("{}", "=".repeat(80));
    println!("Privacy:");
    println!("  • Server learns which entries match (not just existence)");
    println!("  • But cannot learn partial match information");
    println!("  • Blinding prevents learning polynomial structure");
    println!();
    println!("Efficiency:");
    println!("  • Polynomial degree per entry: {}", protocol.entry_polynomials[0].degree());
    println!("  • Number of evaluations: {} (one per entry)", protocol.entry_polynomials.len());
    println!("  • Client sends n results instead of 1 aggregate");
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_entry_matches() {
        let mut query_bits = vec![0; LAMBDA];
        let mut entry_bits = vec![0; LAMBDA];
        
        // Create entry with distance < EPSILON in all blocks
        for block_idx in 0..NUM_BLOCKS {
            for i in 0..(EPSILON - 1) {
                entry_bits[block_idx * BLOCK_SIZE + i] = 1;
            }
        }
        
        let query = BinaryVector::new(query_bits);
        let entry = BinaryVector::new(entry_bits);
        
        let db = Database::new(vec![entry]);
        let mut protocol = TTPProtocol::new(db);
        
        protocol.build_entry_polynomials();
        let res_values = protocol.client_evaluate(&query);
        let (has_match, matches) = protocol.server_check(&res_values);
        
        assert!(has_match);
        assert_eq!(matches, vec![0]);
    }
    
    #[test]
    fn test_no_match() {
        let query_bits = vec![0; LAMBDA];
        let entry_bits = vec![1; LAMBDA];
        
        let query = BinaryVector::new(query_bits);
        let entry = BinaryVector::new(entry_bits);
        
        let db = Database::new(vec![entry]);
        let mut protocol = TTPProtocol::new(db);
        
        protocol.build_entry_polynomials();
        let res_values = protocol.client_evaluate(&query);
        let (has_match, _) = protocol.server_check(&res_values);
        
        assert!(!has_match);
    }
}