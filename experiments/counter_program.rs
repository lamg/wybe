use anchor_lang::prelude::*;

declare_id!("FILL_IN_YOUR_PROGRAM_ID");

#[program]
pub mod counter_program {
    use super::*;

    /// Initialize the counter account, setting it to `start_value`.
    pub fn initialize(ctx: Context<Initialize>, start_value: u64) -> Result<()> {
        // 1) Preconditions about the signer/authority:
        require!(ctx.accounts.user.is_signer, ErrorCode::Unauthorized);

        // 2) Bound the start value
        const MAX_START: u64 = 1_000_000;
        require!(start_value <= MAX_START, ErrorCode::InvalidStartValue);

        let counter = &mut ctx.accounts.counter;
        counter.count = start_value;

        // 3) Postcondition: we really wrote the right value
        assert_eq!(counter.count, start_value);

        Ok(())
    }

    /// Increment the counter by 1, checking for overflow.
    pub fn increment(ctx: Context<Increment>) -> Result<()> {
        // 4) Only the original user may increment
        require!(
            ctx.accounts.counter.user == ctx.accounts.user.key(),
            ErrorCode::Unauthorized
        );

        let counter = &mut ctx.accounts.counter;
        let old = counter.count;

        // 5) No overflow allowed
        require!(old < u64::MAX, ErrorCode::Overflow);

        counter.count = old.checked_add(1).unwrap();

        // 6) Postconditions about monotonicity
        assert_eq!(counter.count, old + 1);
        assert!(counter.count > old);

        Ok(())
    }
}

/// Accounts context for `initialize`
#[derive(Accounts)]
pub struct Initialize<'info> {
    #[account(init, payer = user, space = 8 + 8)]
    pub counter: Account<'info, Counter>,
    #[account(mut)]
    pub user: Signer<'info>,
    pub system_program: Program<'info, System>,
}

/// Accounts context for `increment`
#[derive(Accounts)]
pub struct Increment<'info> {
    #[account(mut, has_one = user)]
    pub counter: Account<'info, Counter>,
    pub user: Signer<'info>,
}

/// The on-chain counter state
#[account]
pub struct Counter {
    pub count: u64,
    pub user: Pubkey,
}

/// Custom errors
#[error_code]
pub enum ErrorCode {
    #[msg("Counter overflow")]
    Overflow,
    #[msg("Unauthorized")]
    Unauthorized,
    #[msg("Start value too large")]
    InvalidStartValue,
}

/*
Proof obligations:

// For `initialize`:
// PO1: ∀ user ∈ Signers (ctx.accounts.user.is_signer)
// PO2: ∀ start_value ≤ MAX_START (start_value ≤ 1_000_000)
// PO3: counter.count_out = start_value

// For `increment`:
// PO4: counter.user = user (ctx.accounts.counter.user == ctx.accounts.user.key())
// PO5: old < u64::MAX
// PO6: counter.count_out = old + 1
// PO7: counter.count_out > counter.count_in

// Global invariants:
// INV1: 0 ≤ counter.count ≤ u64::MAX

// Account-model invariants:
// INV2: counter.owner = program_id
// INV3: counter.rent_exempt = true
*/
