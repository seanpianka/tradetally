-- Add columns to track option split adjustments
-- These store metadata when a trade was affected by a stock/option split

ALTER TABLE trades
ADD COLUMN IF NOT EXISTS option_split_data JSONB DEFAULT NULL;

COMMENT ON COLUMN trades.option_split_data IS 'JSON object containing split adjustment details: {splitRatio, originalStrike, postSplitStrike, splitDate}';

-- Add index for querying split-adjusted trades
CREATE INDEX IF NOT EXISTS idx_trades_option_split_data ON trades USING GIN (option_split_data) WHERE option_split_data IS NOT NULL;
