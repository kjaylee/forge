# Instructions to Deprecate @antinomyhq/forge@0.90.1

## Logging in with a Different npm User

Before attempting to deprecate the package, you need to log in with the appropriate npm user account:

```bash
# Log out of the current npm account
npm logout

# Log in with the different user account
npm login
```

You'll be prompted to enter the username, password, and email for the account. If two-factor authentication is enabled, you'll also need to provide an OTP.

### Verifying User and Ownership

```bash
# Check which user you're currently logged in as
npm whoami

# Verify package ownership to ensure the logged-in user has permissions
npm owner ls @antinomyhq/forge
```

Make sure the user you're logged in as appears in the ownership list before proceeding with deprecation.

### Adding a New Owner (If Needed)

If you need to add a different user as an owner to grant them deprecation privileges:

```bash
# You must be logged in as a current owner to do this
npm owner add <username> @antinomyhq/forge
```

Replace `<username>` with the npm username you want to add as an owner.

There are several approaches you can use to deprecate the package:

## Option 1: Direct Terminal Command (Recommended)

Since two-factor authentication is enabled on your npm account, it's easiest to run the deprecation command directly in your terminal where you can immediately input the OTP when prompted:

```bash
npm deprecate @antinomyhq/forge@0.90.1 "This version is deprecated. Please use the latest version instead."
```

When prompted, enter the OTP from your authenticator app.

## Option 2: Single Command with OTP

Generate a fresh OTP from your authenticator app and use it inline:

```bash
npm deprecate @antinomyhq/forge@0.90.1 "This version is deprecated. Please use the latest version instead." --otp=<CODE>
```

Replace `<CODE>` with your 6-digit OTP code.

## Option 3: Create a New Token with a Longer Expiry

You can create a new npm token with a longer expiration period, which might help avoid OTP issues:

```bash
npm token create --read-only=false
```

Follow the prompts to create the token, then use it for the deprecation.

## Option 4: Use the NPM Registry API Directly

For advanced users, you can use the npm registry API directly with curl:

```bash
# First, get your npm token (this doesn't require an OTP)
npm token create --read-only=false

# Then use curl to update the package
curl -X PUT \
  -H "Authorization: Bearer YOUR_TOKEN" \
  -H "Content-Type: application/json" \
  -d '{"versions":{"0.90.1":{"deprecated":"This version is deprecated. Please use the latest version instead."}}}' \
  https://registry.npmjs.org/@antinomyhq%2Fforge
```

## Verification

After deprecation, verify it worked with:

```bash
npm view @antinomyhq/forge@0.90.1
```

You should see the deprecation message in the output.
