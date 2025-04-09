import { UserButton as ClerkUserButton } from "@clerk/clerk-react";

export function UserButton() {
    return (
        <ClerkUserButton
            afterSignOutUrl="/sign-in"
        />
    );
} 